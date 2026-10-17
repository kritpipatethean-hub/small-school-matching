(function () {
  "use strict";

  var catalog = window.SMS_CATALOG;

  if (!catalog || !Array.isArray(catalog.areas) || !Array.isArray(catalog.provinces)) {
    document.addEventListener("DOMContentLoaded", function () {
      var main = document.getElementById("main-content");
      if (main) {
        var message = document.createElement("p");
        message.className = "status-message";
        message.setAttribute("role", "alert");
        message.textContent = "ไม่สามารถอ่านบัญชีพื้นที่ออฟไลน์ได้ โปรดตรวจว่า catalog-data.js อยู่ข้าง index.html";
        main.prepend(message);
      }
    });
    return;
  }

  var STATUS = {
    ready: {
      label: "พร้อมดู",
      icon: "✓",
      className: "status-ready"
    },
    pending: {
      label: "กำลังจัดทำ",
      icon: "…",
      className: "status-pending"
    },
    blocked: {
      label: "ต้องตรวจข้อมูลต้นทาง",
      icon: "!",
      className: "status-review"
    },
    empty: {
      label: "ไม่มีโรงเรียนขนาดเล็ก",
      icon: "–",
      className: "status-empty"
    }
  };

  var collator = new Intl.Collator("th", { sensitivity: "base", numeric: true });
  var numberFormatter = new Intl.NumberFormat("th-TH");
  var kmFormatter = new Intl.NumberFormat("th-TH", { minimumFractionDigits: 2, maximumFractionDigits: 2 });

  function formatKm(value) {
    return (value === null || typeof value === "undefined") ? "—" : kmFormatter.format(value);
  }
  var focusAfterRoute = null;
  var selectedProvince = "";

  var areas = catalog.areas.map(function (item) {
    return {
      code: String(item.areacode),
      province: item.province,
      name: item.name,
      id: item.id,
      status: item.status,
      summary: item.summary,
      image: item.image,
      pdf: item.pdf,
      sizeImage: item.sizeImage || null,
      sizeProfile: item.sizeProfile || null,
      sizeAnalysis: item.sizeAnalysis || null,
      consolidation: item.consolidation || null,
      analysis: item.analysis,
      updated: item.updated
    };
  }).sort(function (a, b) {
    return collator.compare(a.province, b.province) || collator.compare(a.name, b.name);
  });

  var areaByCode = new Map(areas.map(function (area) { return [area.code, area]; }));
  var areaById = new Map(areas.map(function (area) { return [area.id, area]; }));
  var provinceNames = Array.from(new Set(areas.map(function (area) { return area.province; }))).sort(collator.compare);
  var areasByProvince = new Map(provinceNames.map(function (province) {
    return [province, areas.filter(function (area) { return area.province === province; })];
  }));

  var elements = {};

  function createElement(tag, className, text) {
    var element = document.createElement(tag);
    if (className) {
      element.className = className;
    }
    if (typeof text === "string") {
      element.textContent = text;
    }
    return element;
  }

  function normalize(value) {
    return String(value || "").normalize("NFC").toLocaleLowerCase("th-TH").trim();
  }

  function statusText(statusKey) {
    var status = STATUS[statusKey];
    return status.icon + " " + status.label;
  }

  function makeStatusBadge(statusKey) {
    var badge = createElement("span", "status-badge " + STATUS[statusKey].className, statusText(statusKey));
    return badge;
  }

  function countStatuses(provinceAreas) {
    return provinceAreas.reduce(function (counts, area) {
      counts[area.status] += 1;
      return counts;
    }, { ready: 0, pending: 0, blocked: 0, empty: 0 });
  }

  function provinceMapClass(province) {
    var counts = countStatuses(areasByProvince.get(province) || []);
    if (counts.ready > 0) { return "province-ready"; }
    if (counts.blocked > 0) { return "province-review"; }
    if (counts.empty > 0 && counts.pending === 0) { return "province-empty"; }
    return "province-pending";
  }

  function provinceSummary(province) {
    var provinceAreas = areasByProvince.get(province) || [];
    var counts = countStatuses(provinceAreas);
    var parts = [];
    if (counts.ready) { parts.push("พร้อมดู " + numberFormatter.format(counts.ready) + " พื้นที่"); }
    if (counts.pending) { parts.push("กำลังจัดทำ " + numberFormatter.format(counts.pending) + " พื้นที่"); }
    if (counts.blocked) { parts.push("ต้องตรวจข้อมูลต้นทาง " + numberFormatter.format(counts.blocked) + " พื้นที่"); }
    if (counts.empty) { parts.push("ไม่มีโรงเรียนขนาดเล็ก " + numberFormatter.format(counts.empty) + " พื้นที่"); }
    return parts.join(", ");
  }

  function validateCatalog() {
    var counts = countStatuses(areas);
    var expectedCounts = catalog.meta.statusCounts || {};
    var provinceCatalogNames = new Set(catalog.provinces.map(function (province) { return province.name; }));
    var shapeNames = new Set(Array.from(document.querySelectorAll("#province-map-layers [data-province]")).map(function (shape) {
      return shape.getAttribute("data-province");
    }));
    var valid = areas.length === 183 && provinceNames.length === 77;
    valid = valid && ["ready", "pending", "blocked", "empty"].every(function (status) {
      return Number.isInteger(expectedCounts[status]) && counts[status] === expectedCounts[status];
    });
    valid = valid && provinceNames.every(function (province) { return provinceCatalogNames.has(province) && shapeNames.has(province); });
    if (!valid) {
      console.error("บัญชีพอร์ทัลไม่ผ่านการตรวจจำนวนพื้นที่ จังหวัด สถานะ หรือขอบเขตแผนที่", counts);
    }
  }

  function cacheElements() {
    elements.search = document.getElementById("catalog-search");
    elements.clearSearch = document.getElementById("clear-search");
    elements.searchResults = document.getElementById("search-results");
    elements.searchStatus = document.getElementById("search-status");
    elements.map = document.getElementById("thailand-map");
    elements.mapLayers = document.getElementById("province-map-layers");
    elements.mapFrame = document.querySelector(".map-frame");
    elements.mapTooltip = document.getElementById("map-tooltip");
    elements.resetView = document.getElementById("reset-view");
    elements.provinceSelect = document.getElementById("province-select");
    elements.provinceOverview = document.getElementById("province-overview");
    elements.areaList = document.getElementById("area-list");
    elements.catalogCount = document.getElementById("catalog-count");
    elements.detail = document.getElementById("area-detail");
    elements.detailBack = document.getElementById("detail-back");
    elements.detailCode = document.getElementById("detail-code");
    elements.detailProvince = document.getElementById("detail-province");
    elements.detailTitle = document.getElementById("detail-title");
    elements.detailStatus = document.getElementById("detail-status");
    elements.detailContent = document.getElementById("detail-content");
  }

  // ส่วนบน: ตัวเลขในการ์ดสถานะทุกจุดที่มี data-summary
  function populateSummary() {
    var counts = countStatuses(areas);
    var values = {
      total: areas.length,
      ready: counts.ready,
      pending: counts.pending,
      blocked: counts.blocked,
      empty: counts.empty
    };
    Array.prototype.forEach.call(document.querySelectorAll("[data-summary]"), function (node) {
      var key = node.getAttribute("data-summary");
      if (Object.prototype.hasOwnProperty.call(values, key)) {
        node.textContent = numberFormatter.format(values[key]);
      }
    });
  }

  function populateProvinceSelect() {
    var fragment = document.createDocumentFragment();
    provinceNames.forEach(function (province) {
      var option = document.createElement("option");
      option.value = province;
      option.textContent = province + " — " + (areasByProvince.get(province) || []).length + " สพป.";
      fragment.appendChild(option);
    });
    elements.provinceSelect.appendChild(fragment);
  }

  var tooltipProvince = "";

  function buildTooltipContent(province) {
    var provinceAreas = areasByProvince.get(province) || [];
    var title = createElement("p", "map-tooltip-title", "จังหวัด" + province + " · " + numberFormatter.format(provinceAreas.length) + " สพป.");
    var list = createElement("ul", "map-tooltip-list");
    provinceAreas.forEach(function (area) {
      var item = document.createElement("li");
      item.appendChild(makeStatusBadge(area.status));
      item.appendChild(createElement("span", "", area.name));
      list.appendChild(item);
    });
    var hint = createElement("p", "map-tooltip-hint", "คลิกหรือกด Enter เพื่อเปิดรายชื่อ");
    elements.mapTooltip.replaceChildren(title, list, hint);
    tooltipProvince = province;
  }

  function positionTooltip(clientX, clientY) {
    // เลื่อนกล่องตามตำแหน่งเมาส์ภายในกรอบแผนที่ด้วย CSSOM (CSP style-src อนุญาต ไม่ใช้ style attribute)
    var frame = elements.mapFrame.getBoundingClientRect();
    var tip = elements.mapTooltip;
    var x = clientX - frame.left + 16;
    var y = clientY - frame.top + 16;
    if (x + tip.offsetWidth + 8 > frame.width) {
      x = Math.max(8, clientX - frame.left - tip.offsetWidth - 16);
    }
    if (y + tip.offsetHeight + 8 > frame.height) {
      y = Math.max(8, clientY - frame.top - tip.offsetHeight - 16);
    }
    tip.style.left = Math.round(x) + "px";
    tip.style.top = Math.round(y) + "px";
  }

  function showMapTooltip(province, clientX, clientY) {
    if (!elements.mapTooltip || !elements.mapFrame) { return; }
    if (tooltipProvince !== province) { buildTooltipContent(province); }
    elements.mapTooltip.hidden = false;
    elements.mapTooltip.setAttribute("aria-hidden", "false");
    positionTooltip(clientX, clientY);
  }

  function hideMapTooltip() {
    if (!elements.mapTooltip) { return; }
    elements.mapTooltip.hidden = true;
    elements.mapTooltip.setAttribute("aria-hidden", "true");
  }

  function buildMap() {
    var paths = Array.from(elements.mapLayers.querySelectorAll(".province-shape"));

    paths.forEach(function (path, index) {
      var province = path.getAttribute("data-province");
      var provinceAreas = areasByProvince.get(province) || [];
      var label = "จังหวัด" + province + ": " + provinceSummary(province) + " — " + provinceAreas.map(function (area) {
        return area.name + " (" + STATUS[area.status].label + ")";
      }).join(", ");
      var title = path.querySelector("title");

      path.setAttribute("class", "province-shape " + provinceMapClass(province));
      path.setAttribute("aria-label", label);
      path.setAttribute("aria-pressed", "false");
      // ถอด <title> ออก: ชื่อสำหรับโปรแกรมอ่านหน้าจออยู่ใน aria-label แล้ว และไม่ให้ tooltip ของเบราว์เซอร์ซ้อนกับกล่องชี้จังหวัด
      if (title) { title.remove(); }

      path.addEventListener("pointerenter", function (event) {
        if (event.pointerType === "touch") { return; }
        showMapTooltip(province, event.clientX, event.clientY);
      });
      path.addEventListener("pointermove", function (event) {
        if (event.pointerType === "touch" || elements.mapTooltip.hidden) { return; }
        positionTooltip(event.clientX, event.clientY);
      });
      path.addEventListener("pointerleave", hideMapTooltip);
      path.addEventListener("focus", function () {
        var box = path.getBoundingClientRect();
        showMapTooltip(province, box.right, box.top);
      });
      path.addEventListener("blur", hideMapTooltip);

      path.addEventListener("click", function () {
        hideMapTooltip();
        goToProvince(province, true);
      });

      path.addEventListener("keydown", function (event) {
        if (event.key === "Escape") {
          hideMapTooltip();
          return;
        }
        if (event.key === "Enter" || event.key === " ") {
          event.preventDefault();
          hideMapTooltip();
          goToProvince(province, true);
          return;
        }

        if (["ArrowRight", "ArrowDown", "ArrowLeft", "ArrowUp"].indexOf(event.key) !== -1) {
          event.preventDefault();
          var direction = (event.key === "ArrowRight" || event.key === "ArrowDown") ? 1 : -1;
          var nextIndex = (index + direction + paths.length) % paths.length;
          paths[nextIndex].focus();
        }
      });
    });
  }

  function updateMapSelection(province) {
    selectedProvince = province || "";
    elements.mapLayers.querySelectorAll(".province-shape").forEach(function (path) {
      var selected = path.getAttribute("data-province") === selectedProvince;
      path.classList.toggle("is-selected", selected);
      path.setAttribute("aria-pressed", selected ? "true" : "false");
    });
  }

  function routeHash(type, value) {
    return "#" + type + "=" + encodeURIComponent(value);
  }

  function setRoute(type, value, focusTarget) {
    var nextHash = routeHash(type, value);
    focusAfterRoute = focusTarget || null;
    if (window.location.hash === nextHash) {
      renderRoute();
    } else {
      window.location.hash = nextHash;
    }
  }

  function goToProvince(province, shouldFocus) {
    clearSearch(false);
    setRoute("province", province, shouldFocus ? "province" : null);
  }

  function goToArea(area, shouldFocus) {
    clearSearch(false);
    setRoute("area", area.id, shouldFocus ? "detail" : null);
  }

  function parseRoute() {
    var match = window.location.hash.match(/^#(province|area)=(.*)$/);
    if (!match) {
      return { type: "overview", value: "" };
    }

    try {
      return { type: match[1], value: decodeURIComponent(match[2]) };
    } catch (error) {
      return { type: "overview", value: "" };
    }
  }

  function renderOverview() {
    selectedProvince = "";
    elements.provinceSelect.value = "";
    elements.catalogCount.textContent = "77 จังหวัด";
    elements.provinceOverview.replaceChildren(createElement("p", "", "เลือกจังหวัดเพื่อดูรายชื่อ สพป. และสถานะของแต่ละพื้นที่"));
    elements.areaList.replaceChildren();
    elements.detail.hidden = true;
    updateMapSelection("");
  }

  function renderProvince(province) {
    var provinceAreas = areasByProvince.get(province);
    if (!provinceAreas) {
      renderOverview();
      return false;
    }

    var heading = createElement("h3", "", "จังหวัด" + province);
    heading.tabIndex = -1;
    var summary = createElement("p", "", numberFormatter.format(provinceAreas.length) + " สพป. — " + provinceSummary(province));
    elements.provinceOverview.replaceChildren(heading, summary);
    elements.provinceSelect.value = province;
    elements.catalogCount.textContent = numberFormatter.format(provinceAreas.length) + " สพป.";
    elements.areaList.replaceChildren();

    provinceAreas.forEach(function (area) {
      var button = createElement("button", "area-button");
      button.type = "button";
      button.setAttribute("aria-label", area.name + ", " + STATUS[area.status].label);

      var nameBlock = createElement("span");
      nameBlock.appendChild(createElement("span", "area-name", area.name));
      nameBlock.appendChild(createElement("span", "area-id", "รหัสพื้นที่ " + area.code));
      button.appendChild(nameBlock);
      button.appendChild(makeStatusBadge(area.status));
      button.addEventListener("click", function () { goToArea(area, true); });
      elements.areaList.appendChild(button);
    });

    elements.detail.hidden = true;
    updateMapSelection(province);
    return true;
  }

  function renderMetrics(summary) {
    var labels = {
      registered: "โรงเรียนในทะเบียนพื้นที่",
      origins: "โรงเรียนต้นทางที่วิเคราะห์",
      magnets: "โรงเรียนคุณภาพชุมชน",
      matched: "จับคู่ได้ภายใน 10 กม.",
      over10km: "อยู่นอกเกณฑ์/ไม่ผ่านเกณฑ์",
      unreachable: "ไม่พบเส้นทางในโครงข่าย",
      excluded: "แยกกรณีเป็นโรงเรียนคุณภาพชุมชน",
      coordExceptions: "กรณีพิกัด–ขอบเขตไม่สอดคล้อง"
    };
    var metrics = Object.keys(labels).filter(function (key) {
      return summary && summary[key] !== null && typeof summary[key] !== "undefined";
    }).map(function (key) {
      return { label: labels[key], value: summary[key] };
    });
    var list = createElement("dl", "metrics-grid");
    metrics.forEach(function (metric) {
      var card = createElement("div", "metric");
      card.appendChild(createElement("dt", "", metric.label));
      card.appendChild(createElement("dd", "", numberFormatter.format(metric.value)));
      list.appendChild(card);
    });
    return list;
  }

  function renderDeliverables(detail) {
    var box = createElement("section", "deliverable-box detail-column");
    var heading = createElement("div", "deliverable-heading");
    heading.appendChild(createElement("h3", "", "ผลการจับคู่โรงเรียนขนาดเล็ก"));
    var actions = createElement("div", "deliverable-actions");

    if (detail.pdf) {
      var link = createElement("a", "button", "เปิด PDF สรุปพื้นที่ ↗");
      link.href = detail.pdf;
      link.target = "_blank";
      link.rel = "noopener";
      link.setAttribute("aria-label", "เปิด PDF สรุป " + detail.name + " ในแท็บใหม่");
      actions.appendChild(link);
    } else {
      var disabledButton = createElement("button", "button button-disabled", "ยังไม่ได้บรรจุ PDF");
      disabledButton.type = "button";
      disabledButton.disabled = true;
      actions.appendChild(disabledButton);
    }

    heading.appendChild(actions);
    box.appendChild(heading);

    if (detail.image) {
      var imageLink = createElement("a", "map-open-link");
      imageLink.href = detail.image;
      imageLink.target = "_blank";
      imageLink.rel = "noopener";
      imageLink.setAttribute("aria-label", "เปิดแผนที่ " + detail.name + " ขนาดเต็มในแท็บใหม่ เพื่อขยายอ่านชื่อโรงเรียน");
      var image = document.createElement("img");
      image.className = "result-map-image";
      image.src = detail.image;
      image.alt = "แผนที่สรุปผล " + detail.name;
      image.loading = "lazy";
      image.decoding = "async";
      var help = createElement("p", "help-text map-help", "คลิกแผนที่ หรือกด Tab ไปที่ภาพแล้วกด Enter เพื่อเปิดภาพขนาดเต็มในแท็บใหม่ จากนั้นคลิกภาพเพื่อขยายอ่านชื่อโรงเรียน");
      image.addEventListener("error", function () {
        imageLink.replaceWith(createElement("div", "file-placeholder", "ยังไม่พบภาพ PNG โปรดตรวจว่าโฟลเดอร์ files อยู่ข้าง index.html และมีไฟล์ภาพของพื้นที่นี้"));
        help.remove();
      }, { once: true });
      imageLink.appendChild(image);
      var figure = createElement("figure", "map-figure");
      figure.appendChild(imageLink);
      box.appendChild(figure);
      box.appendChild(help);
    } else {
      box.appendChild(createElement("div", "file-placeholder", "ยังไม่ได้บรรจุภาพ PNG ในชุดพอร์ทัลนี้"));
    }

    return box;
  }

  function renderSizeRow(swatchClass, label, count, total, rowClass) {
    var row = createElement("tr", rowClass);
    var labelCell = document.createElement("td");
    var swatch = createElement("span", "size-swatch " + swatchClass);
    swatch.setAttribute("aria-hidden", "true");
    labelCell.appendChild(swatch);
    labelCell.appendChild(document.createTextNode(label));
    row.appendChild(labelCell);
    row.appendChild(createElement("td", "num", numberFormatter.format(count)));
    row.appendChild(createElement("td", "num", (count / total * 100).toFixed(1)));
    return row;
  }

  function renderSizeSection(detail) {
    var box = createElement("section", "deliverable-box detail-column size-box");
    var maxOnMap = (detail.sizeProfile && detail.sizeProfile.mapMaxStudents) || 60;
    var heading = createElement("div", "deliverable-heading");
    heading.appendChild(createElement("h3", "", "สภาพโรงเรียนขนาดเล็กในพื้นที่"));
    box.appendChild(heading);

    if (detail.sizeImage) {
      var imageLink = createElement("a", "map-open-link");
      imageLink.href = detail.sizeImage;
      imageLink.target = "_blank";
      imageLink.rel = "noopener";
      imageLink.setAttribute("aria-label", "เปิดแผนที่ขนาดโรงเรียน " + detail.name + " ขนาดเต็มในแท็บใหม่");
      var image = document.createElement("img");
      image.className = "result-map-image";
      image.src = detail.sizeImage;
      image.alt = "แผนที่โรงเรียนขนาดเล็กจำแนกตามจำนวนนักเรียน พร้อมชื่อโรงเรียนทุกแห่งที่วาด " + detail.name;
      image.loading = "lazy";
      image.decoding = "async";
      var sizeHelp = createElement("p", "help-text map-help", "แผนที่แสดงเฉพาะโรงเรียนที่มีนักเรียนไม่เกิน " + maxOnMap + " คน พร้อมชื่อโรงเรียนตามทะเบียนของทุกโรงเรียนที่วาด สีและขนาดจุดไล่ตามช่วงจำนวนนักเรียน คลิกภาพ หรือกด Tab ไปที่ภาพแล้วกด Enter เพื่อเปิดภาพขนาดเต็มในแท็บใหม่ แล้วขยายอ่านชื่อโรงเรียน");
      image.addEventListener("error", function () {
        imageLink.replaceWith(createElement("div", "file-placeholder", "ยังไม่พบภาพแผนที่ขนาดโรงเรียน โปรดตรวจว่าโฟลเดอร์ files อยู่ข้าง index.html"));
        sizeHelp.remove();
      }, { once: true });
      imageLink.appendChild(image);
      var sizeFigure = createElement("figure", "map-figure");
      sizeFigure.appendChild(imageLink);
      box.appendChild(sizeFigure);
      box.appendChild(sizeHelp);
    } else {
      box.appendChild(createElement("div", "file-placeholder", "ยังไม่ได้บรรจุแผนที่ขนาดโรงเรียนในชุดพอร์ทัลนี้"));
    }

    var profile = detail.sizeProfile;
    if (profile && Array.isArray(profile.bins) && profile.total) {
      var table = createElement("table", "size-table");
      var caption = createElement("caption", "", "จำนวนโรงเรียนขนาดเล็กทั้งหมดต่อช่วงจำนวนนักเรียนรวม (ตัวเลขรวมระดับพื้นที่ ไม่มีรายโรงเรียน) แถวสีเทาคือช่วงที่ไม่วาดบนแผนที่");
      table.appendChild(caption);
      var head = document.createElement("thead");
      var headRow = document.createElement("tr");
      ["ช่วงจำนวนนักเรียน", "จำนวนโรงเรียน", "ร้อยละ"].forEach(function (label, index) {
        var cell = createElement("th", index ? "num" : "", label);
        cell.scope = "col";
        headRow.appendChild(cell);
      });
      head.appendChild(headRow);
      table.appendChild(head);
      var body = document.createElement("tbody");
      var hiddenBins = [];
      profile.bins.forEach(function (bin, index) {
        if (bin.max > maxOnMap) {
          hiddenBins.push(bin);
          return;
        }
        body.appendChild(renderSizeRow(index <= 5 ? "size-bin-" + index : "size-bin-off", bin.min + "–" + bin.max + " คน", bin.count, profile.total, ""));
      });
      if (hiddenBins.length) {
        var hiddenCount = hiddenBins.reduce(function (sum, bin) { return sum + bin.count; }, 0);
        body.appendChild(renderSizeRow(
          "size-bin-off",
          hiddenBins[0].min + "–" + hiddenBins[hiddenBins.length - 1].max + " คน (ไม่แสดงบนแผนที่)",
          hiddenCount, profile.total, "row-off"
        ));
      }
      table.appendChild(body);
      var foot = document.createElement("tfoot");
      var footRow = document.createElement("tr");
      footRow.appendChild(createElement("th", "", "รวม"));
      footRow.appendChild(createElement("th", "num", numberFormatter.format(profile.total)));
      footRow.appendChild(createElement("th", "num", "100.0"));
      foot.appendChild(footRow);
      table.appendChild(foot);
      box.appendChild(table);
    }

    if (detail.sizeAnalysis) {
      box.appendChild(createElement("p", "size-note", detail.sizeAnalysis));
    }
    return box;
  }

  function renderCompactMetric(label, value, unit) {
    var card = createElement("div", "metric");
    card.appendChild(createElement("dt", "", label));
    card.appendChild(createElement("dd", "", value));
    if (unit) {
      card.appendChild(createElement("dd", "metric-unit", unit));
    }
    return card;
  }

  function renderConsolidationSection(detail) {
    var data = detail.consolidation;
    var section = createElement("section", "deliverable-box consolidation-box");
    var heading = createElement("div", "deliverable-heading");
    heading.appendChild(createElement("h3", "", "ภาพจำลองหากจับคู่ตามผลคัดกรอง"));
    heading.appendChild(createElement("span", "count-chip", "ภาพจำลองประกอบการพิจารณา ไม่ใช่แผนควบรวม"));
    section.appendChild(heading);

    var strip = createElement("dl", "metrics-grid metrics-compact");
    strip.appendChild(renderCompactMetric("โรงเรียน สพป. ในเขต ก่อน → หลัง", numberFormatter.format(data.schoolsBefore) + " → " + numberFormatter.format(data.schoolsAfter), "แห่ง"));
    strip.appendChild(renderCompactMetric("โรงเรียนขนาดเล็กที่จับคู่ได้ / ยังคงอยู่", numberFormatter.format(data.smallMatched) + " / " + numberFormatter.format(data.smallRemaining), "แห่ง จากทะเบียน " + numberFormatter.format(data.smallRegistered) + " แห่ง"));
    strip.appendChild(renderCompactMetric("นักเรียนที่ย้ายตามภาพจำลอง", numberFormatter.format(data.studentsMoved), "คน"));
    strip.appendChild(renderCompactMetric("โรงเรียนคุณภาพชุมชนที่รับนักเรียน", numberFormatter.format(data.qualityReceiving) + " จาก " + numberFormatter.format(data.qualityTotal), "แห่ง"));
    strip.appendChild(renderCompactMetric("ระยะทางคู่ที่จับได้ เฉลี่ย / ไกลสุด", formatKm(data.distanceMeanKm) + " / " + formatKm(data.distanceMaxKm), "กิโลเมตรตามโครงข่ายถนน"));
    section.appendChild(strip);
    section.appendChild(createElement("p", "size-note consolidation-caveat", data.note));

    if (Array.isArray(data.schools) && data.schools.length) {
      var hasSmallFlag = false;
      var wrapper = createElement("div", "table-scroll");
      wrapper.tabIndex = 0;
      wrapper.setAttribute("role", "region");
      wrapper.setAttribute("aria-label", "ตารางโรงเรียนคุณภาพชุมชนตามภาพจำลอง เลื่อนซ้าย–ขวาได้");
      var table = createElement("table", "size-table consolidation-table");
      table.appendChild(createElement("caption", "", "โรงเรียนคุณภาพชุมชนแต่ละแห่งตามภาพจำลอง (นักเรียนตามทะเบียน DMC682 ขนาดตามเกณฑ์ 7 ขนาดของ สพฐ. ตารางนี้ไม่แสดงชื่อโรงเรียนขนาดเล็กต้นทาง)"));
      var head = document.createElement("thead");
      var headRow = document.createElement("tr");
      [
        ["โรงเรียนคุณภาพชุมชน", ""],
        ["นักเรียนก่อน", "num"],
        ["รร.เล็กที่รับ", "num"],
        ["นักเรียนที่รับเพิ่ม", "num"],
        ["นักเรียนหลังรวม", "num"],
        ["ขนาด 7 ระดับ ก่อน → หลัง", ""],
        ["ระยะไกลสุด (กม.)", "num"]
      ].forEach(function (column) {
        var cell = createElement("th", column[1], column[0]);
        cell.scope = "col";
        headRow.appendChild(cell);
      });
      head.appendChild(headRow);
      table.appendChild(head);
      var body = document.createElement("tbody");
      var totals = { before: 0, feeders: 0, received: 0, after: 0 };
      data.schools.forEach(function (school) {
        var row = document.createElement("tr");
        var flag = school.isSmallSchool ? " †" : "";
        if (school.isSmallSchool) { hasSmallFlag = true; }
        row.appendChild(createElement("td", "", school.name + flag));
        row.appendChild(createElement("td", "num", numberFormatter.format(school.studentsBefore)));
        row.appendChild(createElement("td", "num", numberFormatter.format(school.feeders)));
        row.appendChild(createElement("td", "num", numberFormatter.format(school.studentsReceived)));
        row.appendChild(createElement("td", "num", numberFormatter.format(school.studentsAfter)));
        row.appendChild(createElement("td", school.sizeBefore === school.sizeAfter ? "" : "size-shift", school.sizeBefore + " → " + school.sizeAfter));
        row.appendChild(createElement("td", "num", school.feeders ? formatKm(school.farthestKm) : "—"));
        body.appendChild(row);
        totals.before += school.studentsBefore;
        totals.feeders += school.feeders;
        totals.received += school.studentsReceived;
        totals.after += school.studentsAfter;
      });
      table.appendChild(body);
      var foot = document.createElement("tfoot");
      var footRow = document.createElement("tr");
      footRow.appendChild(createElement("th", "", "รวม / ไกลสุด"));
      footRow.appendChild(createElement("th", "num", numberFormatter.format(totals.before)));
      footRow.appendChild(createElement("th", "num", numberFormatter.format(totals.feeders)));
      footRow.appendChild(createElement("th", "num", numberFormatter.format(totals.received)));
      footRow.appendChild(createElement("th", "num", numberFormatter.format(totals.after)));
      footRow.appendChild(createElement("td", "", ""));
      footRow.appendChild(createElement("th", "num", formatKm(data.distanceMaxKm)));
      foot.appendChild(footRow);
      table.appendChild(foot);
      wrapper.appendChild(table);
      section.appendChild(wrapper);
      if (hasSmallFlag) {
        section.appendChild(createElement("p", "help-text", "† โรงเรียนขนาดเล็กตามทะเบียนที่มีบทบาทโรงเรียนคุณภาพชุมชนด้วย จึงนับอยู่ในกลุ่มที่ยังคงอยู่และเป็นปลายทางรับนักเรียนพร้อมกัน"));
      }
    }
    return section;
  }

  function renderReadyDetail(area, detail) {
    var fragment = document.createDocumentFragment();
    fragment.appendChild(renderMetrics(detail.summary));

    var grid = createElement("div", "detail-grid");
    var deliverables = renderDeliverables(detail);
    var analysis = createElement("section", "analysis-box");
    analysis.appendChild(createElement("h4", "", "บทวิเคราะห์สั้น"));
    analysis.appendChild(createElement("p", "", detail.analysis));
    if (detail.updated) {
      analysis.appendChild(createElement("p", "help-text", "ข้อมูลสรุปปรับปรุงล่าสุด " + detail.updated));
    }
    deliverables.appendChild(analysis);
    grid.appendChild(deliverables);
    grid.appendChild(renderSizeSection(detail));
    fragment.appendChild(grid);
    if (detail.consolidation) {
      fragment.appendChild(renderConsolidationSection(detail));
    }
    return fragment;
  }

  function renderUnavailableDetail(area) {
    var box = createElement("section", "status-message");
    var title;
    var message;

    if (area.status === "blocked") {
      title = "พื้นที่นี้ต้องตรวจข้อมูลขอบเขตต้นทาง";
      message = "มีพื้นที่นี้ในข้อมูลโรงเรียน แต่ยังไม่มีขอบเขตแยกที่ตรงกัน จึงระงับการเผยแพร่ผลจนกว่าจะตรวจและยืนยันข้อมูลต้นทางแล้ว";
    } else if (area.status === "empty") {
      title = "ไม่มีโรงเรียนขนาดเล็กในข้อมูล DMC ของเขตนี้";
      message = "เขตนี้ยังอยู่ในรายชื่อ 183 สพป. เพื่อให้ครบถ้วน แต่ข้อมูล DMC ของ สพฐ. ปีการศึกษา 2568 ภาคเรียนที่ 2 ไม่มีโรงเรียนขนาดเล็กให้วิเคราะห์";
    } else {
      title = "ผลอยู่ระหว่างจัดทำ";
      message = "ยังไม่มีผลที่ผ่านการตรวจรับสำหรับเผยแพร่ในพอร์ทัล โปรดกลับมาตรวจในชุดส่งมอบรุ่นถัดไป";
    }

    box.appendChild(createElement("h3", "", title));
    box.appendChild(createElement("p", "", message));
    return box;
  }

  function renderArea(area) {
    if (!renderProvince(area.province)) {
      return false;
    }

    elements.detailBack.href = routeHash("province", area.province);
    elements.detailCode.textContent = area.id;
    elements.detailProvince.textContent = "จังหวัด" + area.province;
    elements.detailTitle.textContent = area.name;
    elements.detailTitle.tabIndex = -1;
    elements.detailStatus.className = "status-badge " + STATUS[area.status].className;
    elements.detailStatus.textContent = statusText(area.status);
    elements.detailContent.replaceChildren();

    if (area.status === "ready") {
      elements.detailContent.appendChild(renderReadyDetail(area, area));
    } else {
      elements.detailContent.appendChild(renderUnavailableDetail(area));
    }

    elements.detail.hidden = false;
    return true;
  }

  function renderRoute() {
    var route = parseRoute();
    var rendered = false;

    if (route.type === "area") {
      var area = areaById.get(route.value) || areaByCode.get(route.value.replace(/^spap-/, ""));
      if (area) {
        rendered = renderArea(area);
      }
    } else if (route.type === "province") {
      rendered = renderProvince(route.value);
    }

    if (!rendered) {
      renderOverview();
    }

    if (focusAfterRoute === "detail" && !elements.detail.hidden) {
      elements.detail.scrollIntoView({ block: "start" });
      elements.detailTitle.focus({ preventScroll: true });
    } else if (focusAfterRoute === "province") {
      var provinceHeading = elements.provinceOverview.querySelector("h3");
      if (provinceHeading) {
        provinceHeading.focus();
      }
    } else if (focusAfterRoute === "overview") {
      elements.provinceSelect.focus();
    }
    focusAfterRoute = null;
  }

  function handleHashChange() {
    var route = parseRoute();
    var active = document.activeElement;
    if (active && elements.detail.contains(active) && route.type !== "area") {
      focusAfterRoute = route.type === "province" ? "province" : "overview";
    }
    renderRoute();
  }

  function makeResultButton(primary, secondary, onClick) {
    var button = createElement("button", "result-button");
    button.type = "button";
    button.appendChild(createElement("span", "area-name", primary));
    button.appendChild(createElement("span", "result-meta", secondary));
    button.addEventListener("click", onClick);
    return button;
  }

  function appendResultSection(title, matches, renderButton) {
    if (!matches.length) {
      return;
    }
    elements.searchResults.appendChild(createElement("h3", "", title));
    var list = createElement("ul", "result-list");
    matches.forEach(function (match) {
      var item = document.createElement("li");
      item.appendChild(renderButton(match));
      list.appendChild(item);
    });
    elements.searchResults.appendChild(list);
  }

  function renderSearchResults() {
    var query = normalize(elements.search.value);
    elements.clearSearch.hidden = !query;
    elements.searchResults.replaceChildren();

    if (!query) {
      elements.searchResults.hidden = true;
      elements.searchStatus.textContent = "";
      return;
    }

    var provinceMatches = provinceNames.filter(function (province) {
      return normalize(province).includes(query) || normalize("จังหวัด" + province).includes(query);
    });

    var areaMatches = areas.filter(function (area) {
      var searchable = [area.name, area.province, area.code, area.id].map(normalize).join(" ");
      return searchable.includes(query);
    });

    appendResultSection("จังหวัด", provinceMatches, function (province) {
      return makeResultButton("จังหวัด" + province, (areasByProvince.get(province) || []).length + " สพป. — " + provinceSummary(province), function () {
        goToProvince(province, true);
      });
    });

    appendResultSection("สำนักงานเขตพื้นที่การศึกษาประถมศึกษา", areaMatches, function (area) {
      return makeResultButton(area.name, "จังหวัด" + area.province + " · " + area.code + " · " + statusText(area.status), function () {
        goToArea(area, true);
      });
    });

    var total = provinceMatches.length + areaMatches.length;
    if (!total) {
      elements.searchResults.appendChild(createElement("p", "status-message", "ไม่พบจังหวัดหรือ สพป. ที่ตรงกับคำค้น"));
    }
    elements.searchResults.hidden = false;
    elements.searchStatus.textContent = "พบ " + numberFormatter.format(total) + " รายการ";
  }

  function clearSearch(shouldFocus) {
    elements.search.value = "";
    renderSearchResults();
    if (shouldFocus) {
      elements.search.focus();
    }
  }

  function bindEvents() {
    elements.search.addEventListener("input", renderSearchResults);
    elements.search.addEventListener("keydown", function (event) {
      if (event.key === "Escape") {
        clearSearch(true);
      }
    });
    elements.clearSearch.addEventListener("click", function () { clearSearch(true); });
    elements.provinceSelect.addEventListener("change", function () {
      if (elements.provinceSelect.value) {
        goToProvince(elements.provinceSelect.value, true);
      } else if (window.location.hash) {
        window.location.hash = "";
      } else {
        renderOverview();
      }
    });
    elements.resetView.addEventListener("click", function () {
      clearSearch(false);
      focusAfterRoute = "province";
      if (window.location.hash) {
        window.location.hash = "";
      } else {
        renderOverview();
      }
      elements.provinceSelect.focus();
    });
    elements.detailBack.addEventListener("click", function () {
      focusAfterRoute = "province";
    });
    window.addEventListener("hashchange", handleHashChange);
  }

  function init() {
    cacheElements();
    validateCatalog();
    populateSummary();
    populateProvinceSelect();
    buildMap();
    bindEvents();
    renderRoute();
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init, { once: true });
  } else {
    init();
  }
}());
