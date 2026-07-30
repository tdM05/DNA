const state = {
  summary: null,
  lean: null,
  scores: null,
  liveTimers: [],
  refreshInFlight: {
    summary: false,
    lean: false,
    scores: false,
  },
  scoreFilters: {
    reviewers: [],
    propositions: [],
    reviewerStatus: "all",
  },
  exportFilters: {
    reviewers: [],
    reviewerStatus: "all",
  },
  expanders: {
    recentWarmups: false,
  },
};

const $ = (id) => document.getElementById(id);

function escapeHtml(text) {
  return String(text ?? "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}

const easternDateTime = new Intl.DateTimeFormat("en-US", {
  timeZone: "America/New_York",
  year: "numeric",
  month: "2-digit",
  day: "2-digit",
  hour: "2-digit",
  minute: "2-digit",
  second: "2-digit",
  hour12: false,
  timeZoneName: "short",
});

function formatEasternTime(value) {
  if (!value) return "";
  const date = new Date(String(value));
  if (Number.isNaN(date.getTime())) return String(value);
  return easternDateTime.format(date);
}

function withEasternFilename(filename) {
  return String(filename || "export")
    .replace(/(\.json|\.csv)$/i, "_eastern$1");
}

async function api(path, opts = {}) {
  const res = await fetch(path, {
    headers: { "Content-Type": "application/json", ...(opts.headers || {}) },
    ...opts,
  });
  if (!res.ok) {
    let message = `${res.status} ${res.statusText}`;
    try {
      const data = await res.json();
      message = data.error || message;
    } catch (_) {}
    throw new Error(message);
  }
  return res.json();
}

function showLogin(message = "") {
  $("loginView").classList.remove("hidden");
  $("adminApp").classList.add("hidden");
  $("loginMessage").textContent = message;
}

function showAdmin() {
  $("loginView").classList.add("hidden");
  $("adminApp").classList.remove("hidden");
  if ($("inviteAccessUrl") && !$("inviteAccessUrl").value) {
    $("inviteAccessUrl").value = window.location.origin;
  }
}

function pill(label, cls = "") {
  return `<span class="pill ${escapeHtml(cls)}">${escapeHtml(label)}</span>`;
}

function countList(items, empty = "None") {
  if (!items?.length) return `<span class="compact">${escapeHtml(empty)}</span>`;
  const preview = items.slice(0, 8).join(", ");
  const suffix = items.length > 8 ? `, +${items.length - 8} more` : "";
  return `<span class="compact">${escapeHtml(preview + suffix)}</span>`;
}

function expandableCountList(key, items, empty = "None", limit = 8) {
  if (!items?.length) return `<span class="compact">${escapeHtml(empty)}</span>`;
  const preview = items.slice(0, limit).join(", ");
  const remaining = items.slice(limit);
  if (!remaining.length) return `<span class="compact">${escapeHtml(preview)}</span>`;
  const open = Boolean(state.expanders[key]);
  return `
    <span class="compact">${escapeHtml(preview)}</span>
    ${open ? `<span class="compact list-expanded-items">${escapeHtml(remaining.join(", "))}</span>` : ""}
    <button class="list-expander" type="button" data-expander="${escapeHtml(key)}">
      ${open ? "Collapse" : `+${escapeHtml(remaining.length)} more`}
    </button>
  `;
}

function bindExpanders(root = document) {
  root.querySelectorAll("button[data-expander]").forEach((node) => {
    node.addEventListener("click", () => {
      state.expanders[node.dataset.expander] = !state.expanders[node.dataset.expander];
      if (state.lean) renderLeanStatus(state.lean);
    });
  });
}

function selectedValues(select) {
  return Array.from(select?.selectedOptions || []).map((option) => option.value);
}

function methodLabel(methodId) {
  const method = (state.scores?.methods || []).find((item) => item.id === methodId);
  const label = method?.label || methodId;
  return /^Formalization [AB]$/i.test(label) ? methodId : label;
}

function downloadText(filename, text, type) {
  const blob = new Blob([text], { type });
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = url;
  link.download = filename;
  document.body.appendChild(link);
  link.click();
  link.remove();
  URL.revokeObjectURL(url);
}

function exportFilenameFromResponse(response, fallback) {
  const header = response.headers.get("Content-Disposition") || "";
  const match = header.match(/filename="([^"]+)"/i) || header.match(/filename=([^;]+)/i);
  return match ? match[1].trim() : fallback;
}

function addEasternTimesToJson(value) {
  if (Array.isArray(value)) return value.map(addEasternTimesToJson);
  if (!value || typeof value !== "object") return value;
  const out = {};
  for (const [key, item] of Object.entries(value)) {
    out[key] = addEasternTimesToJson(item);
    if (/_at$/.test(key) && item) out[`${key}_eastern`] = formatEasternTime(item);
  }
  return out;
}

function parseCsv(text) {
  const rows = [];
  let row = [];
  let field = "";
  let quoted = false;
  for (let i = 0; i < text.length; i += 1) {
    const ch = text[i];
    const next = text[i + 1];
    if (quoted) {
      if (ch === '"' && next === '"') {
        field += '"';
        i += 1;
      } else if (ch === '"') {
        quoted = false;
      } else {
        field += ch;
      }
    } else if (ch === '"') {
      quoted = true;
    } else if (ch === ",") {
      row.push(field);
      field = "";
    } else if (ch === "\n") {
      row.push(field);
      rows.push(row);
      row = [];
      field = "";
    } else if (ch !== "\r") {
      field += ch;
    }
  }
  if (field || row.length) {
    row.push(field);
    rows.push(row);
  }
  return rows;
}

function csvCell(value) {
  const text = String(value ?? "");
  return /[",\n\r]/.test(text) ? `"${text.replaceAll('"', '""')}"` : text;
}

function addEasternTimesToCsv(text) {
  const rows = parseCsv(text);
  if (!rows.length) return text;
  const headers = rows[0];
  const timeIndexes = headers
    .map((header, index) => (/_at$/.test(header) ? index : -1))
    .filter((index) => index >= 0);
  if (!timeIndexes.length) return text;
  const outHeaders = [...headers, ...timeIndexes.map((index) => `${headers[index]}_eastern`)];
  const outRows = rows.slice(1).map((row) => [
    ...row,
    ...timeIndexes.map((index) => formatEasternTime(row[index] || "")),
  ]);
  return [outHeaders, ...outRows].map((row) => row.map(csvCell).join(",")).join("\n") + "\n";
}

function exportReviewerCodeSet() {
  return new Set(selectedExportReviewers().map((reviewer) => reviewer.reviewer_code));
}

function filterExportJson(data) {
  const reviewerCodes = exportReviewerCodeSet();
  const keepRows = (rows) => Array.isArray(rows)
    ? rows.filter((row) => reviewerCodes.has(row?.reviewer_code))
    : rows;
  return {
    ...data,
    reviewer_scope: state.exportFilters.reviewers.length ? "selected_reviewers" : "active_reviewers",
    reviewer_status: state.exportFilters.reviewerStatus,
    reviewer_codes: Array.from(reviewerCodes).sort(),
    responses: keepRows(data.responses),
    preference_responses: keepRows(data.preference_responses),
    overall_notes: keepRows(data.overall_notes),
  };
}

function filterExportCsv(text) {
  const rows = parseCsv(text);
  if (!rows.length) return text;
  const reviewerIndex = rows[0].indexOf("reviewer_code");
  if (reviewerIndex < 0) return text;
  const reviewerCodes = exportReviewerCodeSet();
  return [
    rows[0],
    ...rows.slice(1).filter((row) => reviewerCodes.has(row[reviewerIndex] || "")),
  ].map((row) => row.map(csvCell).join(",")).join("\n") + "\n";
}

async function downloadEasternExport(link) {
  const href = link.getAttribute("href");
  if (!href) return;
  const response = await fetch(href, { headers: { Accept: "*/*" } });
  if (!response.ok) throw new Error(`${response.status} ${response.statusText}`);
  const fallback = href.includes(".json") ? "responses.json" : "responses.csv";
  const filename = withEasternFilename(exportFilenameFromResponse(response, fallback));
  const text = await response.text();
  if (filename.toLowerCase().endsWith(".json")) {
    const data = addEasternTimesToJson(filterExportJson(JSON.parse(text)));
    downloadText(filename, JSON.stringify(data, null, 2) + "\n", "application/json; charset=utf-8");
    return;
  }
  downloadText(filename, addEasternTimesToCsv(filterExportCsv(text)), "text/csv; charset=utf-8");
}

function metricChartLabel(title) {
  return String(title || "")
    .replace(/\s+Fidelity$/i, "")
    .replace(/^Proof-Step$/i, "Step Coverage")
    .replace(/^Assumption and Side-Condition$/i, "Assumptions")
    .replace(/^Cited-Dependency$/i, "Dependencies");
}

function renderSummaryCards(summary) {
  const cards = [
    ["Propositions", summary.proposition_count],
    ["Ready pairs", summary.ready_proposition_count],
    ["Enabled reviewers", summary.active_reviewer_count],
    ["Recent reviewers", summary.recent_active_reviewer_count || 0],
    ["Started", summary.started_reviewer_count],
    ["Done", summary.done_reviewer_count],
  ];
  $("summaryCards").innerHTML = cards.map(([label, value]) => `
    <article class="stat-card">
      <b>${escapeHtml(value)}</b>
      <span>${escapeHtml(label)}</span>
    </article>
  `).join("");
}

function renderScoreFilterOptions() {
  const reviewerSelect = $("reviewerFilter");
  const propSelect = $("propFilter");
  const activeReviewers = (state.summary?.reviewers || []).filter((reviewer) => reviewer.active);
  reviewerSelect.innerHTML = activeReviewers.map((reviewer) => `
    <option value="${escapeHtml(reviewer.reviewer_code)}" ${state.scoreFilters.reviewers.includes(reviewer.reviewer_code) ? "selected" : ""}>
      ${escapeHtml(reviewer.reviewer_code)} (${escapeHtml(reviewer.status.replace("_", " "))})
    </option>
  `).join("");
  propSelect.innerHTML = (state.scores?.propositions || []).map((prop) => `
    <option value="${escapeHtml(prop.id)}" ${state.scoreFilters.propositions.includes(prop.id) ? "selected" : ""}>
      ${escapeHtml(prop.display)}
    </option>
  `).join("");
  $("reviewerStatusFilter").value = state.scoreFilters.reviewerStatus;
}

function selectedExportReviewers() {
  const filters = state.exportFilters;
  return (state.summary?.reviewers || []).filter((reviewer) => (
    reviewer.active
    && (!filters.reviewers.length || filters.reviewers.includes(reviewer.reviewer_code))
    && (filters.reviewerStatus === "all" || reviewer.status === filters.reviewerStatus)
  ));
}

function exportQueryString() {
  const params = new URLSearchParams();
  params.set("reviewers", "active");
  if (state.exportFilters.reviewerStatus !== "all") {
    params.set("reviewer_status", state.exportFilters.reviewerStatus);
  }
  if (state.exportFilters.reviewers.length) {
    params.set("reviewer_codes", state.exportFilters.reviewers.join(","));
  }
  const text = params.toString();
  return text ? `?${text}` : "";
}

function updateExportLinks() {
  const query = exportQueryString();
  const links = [
    ["exportResponsesJson", "/api/admin/exports/responses.json"],
    ["exportResponsesCsv", "/api/admin/exports/responses.csv"],
    ["exportPreferencesCsv", "/api/admin/exports/preference_responses.csv"],
  ];
  for (const [id, base] of links) {
    const link = $(id);
    if (link) link.href = `${base}${query}`;
  }
  const count = selectedExportReviewers().length;
  const status = state.exportFilters.reviewerStatus === "all"
    ? "active"
    : state.exportFilters.reviewerStatus.replace("_", " ");
  const picked = state.exportFilters.reviewers.length
    ? ` from ${state.exportFilters.reviewers.length} selected code(s)`
    : "";
  if ($("exportFilterSummary")) {
    $("exportFilterSummary").textContent = `Exports include ${count} ${status} reviewer(s)${picked}.`;
  }
}

function renderExportFilterOptions() {
  const reviewerSelect = $("exportReviewerFilter");
  if (!reviewerSelect) return;
  const activeReviewers = (state.summary?.reviewers || []).filter((reviewer) => reviewer.active);
  const activeCodes = new Set(activeReviewers.map((reviewer) => reviewer.reviewer_code));
  state.exportFilters.reviewers = state.exportFilters.reviewers.filter((code) => activeCodes.has(code));
  reviewerSelect.innerHTML = activeReviewers.map((reviewer) => `
    <option value="${escapeHtml(reviewer.reviewer_code)}" ${state.exportFilters.reviewers.includes(reviewer.reviewer_code) ? "selected" : ""}>
      ${escapeHtml(reviewer.reviewer_code)} (${escapeHtml(reviewer.status.replace("_", " "))})
    </option>
  `).join("");
  $("exportReviewerStatusFilter").value = state.exportFilters.reviewerStatus;
  updateExportLinks();
}

function filteredScoreRows() {
  const filters = state.scoreFilters;
  const reviewerMap = new Map((state.summary?.reviewers || []).map((reviewer) => [reviewer.reviewer_code, reviewer]));
  const propMap = new Map((state.scores?.propositions || []).map((prop) => [prop.id, prop]));
  return (state.scores?.responses || []).filter((row) => {
    const reviewer = reviewerMap.get(row.reviewer_code);
    const prop = propMap.get(row.proposition_id);
    if (!reviewer?.active || !prop) return false;
    if (filters.reviewers.length && !filters.reviewers.includes(row.reviewer_code)) return false;
    if (filters.propositions.length && !filters.propositions.includes(row.proposition_id)) return false;
    if (filters.reviewerStatus !== "all" && reviewer.status !== filters.reviewerStatus) return false;
    return true;
  });
}

function filteredPreferenceRows() {
  const filters = state.scoreFilters;
  const reviewerMap = new Map((state.summary?.reviewers || []).map((reviewer) => [reviewer.reviewer_code, reviewer]));
  const propMap = new Map((state.scores?.propositions || []).map((prop) => [prop.id, prop]));
  return (state.scores?.preference_responses || []).filter((row) => {
    const reviewer = reviewerMap.get(row.reviewer_code);
    const prop = propMap.get(row.proposition_id);
    if (!reviewer?.active || !prop) return false;
    if (filters.reviewers.length && !filters.reviewers.includes(row.reviewer_code)) return false;
    if (filters.propositions.length && !filters.propositions.includes(row.proposition_id)) return false;
    if (filters.reviewerStatus !== "all" && reviewer.status !== filters.reviewerStatus) return false;
    return true;
  });
}

function aggregateScores(rows) {
  const metrics = state.scores?.metrics || [];
  const methodIds = (state.scores?.methods || []).map((method) => method.id);
  const data = Object.fromEntries(methodIds.map((methodId) => [
    methodId,
    Object.fromEntries(metrics.map((metric) => [metric.id, { sum: 0, count: 0, avg: null }])),
  ]));
  for (const row of rows) {
    const slot = data[row.method_id]?.[row.metric_id];
    if (!slot || typeof row.score !== "number") continue;
    slot.sum += row.score;
    slot.count += 1;
  }
  for (const methodId of methodIds) {
    for (const metric of metrics) {
      const slot = data[methodId][metric.id];
      slot.avg = slot.count ? slot.sum / slot.count : null;
    }
  }
  return data;
}

function aggregatePreferences(rows) {
  const questions = state.scores?.preference_questions || [];
  const data = Object.fromEntries(questions.map((question) => [question.id, { sum: 0, count: 0, avg: null }]));
  for (const row of rows) {
    const slot = data[row.question_id];
    if (!slot || typeof row.choice !== "number") continue;
    slot.sum += row.choice;
    slot.count += 1;
  }
  for (const question of questions) {
    const slot = data[question.id];
    slot.avg = slot.count ? slot.sum / slot.count : null;
  }
  return data;
}

function preferenceScaleMethods() {
  const scale = state.scores?.preference_choice_scale || {};
  return {
    negative: scale.negative_method_id || "leaneuclid",
    positive: scale.positive_method_id || "new_method",
  };
}

function renderScoreChart(scoreAggregates, preferenceAggregates, scoreRows, preferenceRows) {
  const metrics = state.scores?.metrics || [];
  const methodIds = (state.scores?.methods || []).map((method) => method.id);
  const questions = state.scores?.preference_questions || [];
  if (!metrics.length || !methodIds.length) {
    $("scoreChart").innerHTML = `<div class="health-item">No score data shape is available.</div>`;
    $("scoreLegend").innerHTML = "";
    $("scoreSummary").textContent = "";
    return;
  }
  const metric = metrics[0];
  const preferenceScale = preferenceScaleMethods();
  $("scoreChart").innerHTML = `
    <div class="chart-grid">
      <section class="step-bars" aria-label="Step metric averages">
        <h3>${escapeHtml(metric.title || "Step metric")}</h3>
        ${methodIds.map((methodId, idx) => {
          const slot = scoreAggregates[methodId]?.[metric.id];
          const avg = slot?.avg;
          const max = metric.max_score || 5;
          const pct = avg === null || avg === undefined ? 0 : Math.max(0, Math.min(100, (avg / max) * 100));
          return `
            <div class="bar-row">
              <div class="bar-label">
                <b>${escapeHtml(methodLabel(methodId))}</b>
                <span>${avg === null || avg === undefined ? "n/a" : avg.toFixed(2)} / ${escapeHtml(max)} · n=${escapeHtml(slot?.count || 0)}</span>
              </div>
              <div class="bar-track">
                <span class="bar-fill method-${idx === 0 ? "old" : "new"}" style="width:${pct.toFixed(1)}%"></span>
              </div>
            </div>
          `;
        }).join("")}
      </section>
      <section class="comparison-scales" aria-label="Comparison averages">
        <h3>Comparisons</h3>
        ${questions.map((question) => {
          const slot = preferenceAggregates[question.id];
          const avg = slot?.avg;
          const pct = avg === null || avg === undefined ? 50 : ((Math.max(-3, Math.min(3, avg)) + 3) / 6) * 100;
          return `
            <div class="scale-row">
              <div class="scale-label">
                <b>${escapeHtml(question.title)}</b>
                <span>${avg === null || avg === undefined ? "n/a" : avg.toFixed(2)} · n=${escapeHtml(slot?.count || 0)}</span>
              </div>
              <div class="scale-track">
                <span class="scale-mid"></span>
                <span class="scale-thumb" style="left:${pct.toFixed(1)}%"></span>
              </div>
              <div class="scale-ends"><span>${escapeHtml(methodLabel(preferenceScale.negative))}</span><span>Neutral</span><span>${escapeHtml(methodLabel(preferenceScale.positive))}</span></div>
            </div>
          `;
        }).join("")}
      </section>
    </div>
  `;
  $("scoreLegend").innerHTML = methodIds.map((methodId, idx) => `
    <span class="legend-item"><span class="legend-swatch ${idx === 0 ? "old" : "new"}"></span>${escapeHtml(methodLabel(methodId))}</span>
  `).join("");
  const propCount = new Set([...scoreRows, ...preferenceRows].map((row) => row.proposition_id)).size;
  const reviewerCount = new Set([...scoreRows, ...preferenceRows].map((row) => row.reviewer_code)).size;
  const averages = methodIds.map((methodId) => {
    const values = metrics.map((item) => scoreAggregates[methodId]?.[item.id]?.avg).filter((value) => value !== null && value !== undefined);
    const avg = values.length ? values.reduce((a, b) => a + b, 0) / values.length : null;
    return `${methodLabel(methodId)} ${avg === null ? "n/a" : avg.toFixed(2)}`;
  }).join("; ");
  $("scoreSummary").textContent = `${scoreRows.length} step scores and ${preferenceRows.length} comparison choices from ${reviewerCount} reviewer(s) and ${propCount} proposition(s). Step means: ${averages}.`;
}

function renderScoreBreakdown(scoreAggregates, preferenceAggregates) {
  const metrics = state.scores?.metrics || [];
  const methodIds = (state.scores?.methods || []).map((method) => method.id);
  const preferenceScale = preferenceScaleMethods();
  const metricRows = metrics.map((metric) => `
    <tr>
      <td><b>${escapeHtml(metric.title)}</b></td>
      ${methodIds.map((methodId) => {
        const slot = scoreAggregates[methodId]?.[metric.id];
        const value = slot?.avg === null || slot?.avg === undefined ? "n/a" : slot.avg.toFixed(2);
        return `<td>${escapeHtml(value)} <span class="compact">n=${escapeHtml(slot?.count || 0)}</span></td>`;
      }).join("")}
    </tr>
  `).join("");
  const preferenceRows = (state.scores?.preference_questions || []).map((question) => {
    const slot = preferenceAggregates[question.id];
    const value = slot?.avg === null || slot?.avg === undefined ? "n/a" : slot.avg.toFixed(2);
    return `
      <tr>
        <td><b>${escapeHtml(question.title)}</b></td>
        <td colspan="${escapeHtml(methodIds.length)}">${escapeHtml(value)} <span class="compact">n=${escapeHtml(slot?.count || 0)}; -3 favors ${escapeHtml(methodLabel(preferenceScale.negative))}, +3 favors ${escapeHtml(methodLabel(preferenceScale.positive))}</span></td>
      </tr>
    `;
  }).join("");
  return `
    <div class="table-wrap score-breakdown">
      <table>
        <thead>
          <tr>
            <th>Item</th>
            ${methodIds.map((methodId) => `<th>${escapeHtml(methodLabel(methodId))}</th>`).join("")}
          </tr>
        </thead>
        <tbody>${metricRows}${preferenceRows}</tbody>
      </table>
    </div>
  `;
}

function renderScoreAnalytics() {
  renderScoreFilterOptions();
  const scoreRows = filteredScoreRows();
  const preferenceRows = filteredPreferenceRows();
  const scoreAggregates = aggregateScores(scoreRows);
  const preferenceAggregates = aggregatePreferences(preferenceRows);
  renderScoreChart(scoreAggregates, preferenceAggregates, scoreRows, preferenceRows);
  $("scoreBreakdown").innerHTML = renderScoreBreakdown(scoreAggregates, preferenceAggregates);
}

function renderReviewers(summary) {
  $("reviewerRows").innerHTML = summary.reviewers.map((reviewer) => {
    const statusClass = reviewer.active ? reviewer.status : "disabled";
    const statusText = reviewer.active ? reviewer.status.replace("_", " ") : "disabled";
    const itemCount = Number(reviewer.response_count || 0) + Number(reviewer.preference_response_count || 0);
    const requiredCount = Number(reviewer.required_response_count || 0) + Number(reviewer.required_preference_response_count || 0);
    return `
      <tr>
        <td><b>${escapeHtml(reviewer.reviewer_code)}</b></td>
        <td>${pill(statusText, statusClass)}</td>
        <td>
          ${escapeHtml(itemCount)} / ${escapeHtml(requiredCount)}
          <div class="compact">${escapeHtml(reviewer.response_count || 0)} step; ${escapeHtml(reviewer.preference_response_count || 0)} comparison</div>
        </td>
        <td>${reviewer.tutorial_completed ? pill("complete", "done") : pill("not complete", "not_started")}</td>
        <td class="compact">${escapeHtml(reviewer.last_activity ? formatEasternTime(reviewer.last_activity) : "No activity")}</td>
        <td class="reviewer-actions">
          <button data-reviewer-toggle="${escapeHtml(reviewer.reviewer_code)}" data-disabled="${reviewer.active ? "true" : "false"}" type="button">
            ${reviewer.active ? "Disable" : "Enable"}
          </button>
          <button class="danger" data-reviewer-remove="${escapeHtml(reviewer.reviewer_code)}" type="button" ${reviewer.active ? "disabled" : ""}>
            Remove
          </button>
        </td>
      </tr>
    `;
  }).join("");
  document.querySelectorAll("[data-reviewer-toggle]").forEach((button) => {
    button.addEventListener("click", async () => {
      await api("/api/admin/reviewers/disable", {
        method: "POST",
        body: JSON.stringify({
          reviewer_code: button.dataset.reviewerToggle,
          disabled: button.dataset.disabled === "true",
        }),
      });
      await loadAdminData();
    });
  });
  document.querySelectorAll("[data-reviewer-remove]").forEach((button) => {
    button.addEventListener("click", async () => {
      const code = button.dataset.reviewerRemove;
      const ok = window.confirm(`Remove reviewer code "${code}" from the admin list? Existing saved responses are preserved in exports, but this code will no longer be accepted.`);
      if (!ok) return;
      await api("/api/admin/reviewers/remove", {
        method: "POST",
        body: JSON.stringify({ reviewer_code: code }),
      });
      await loadAdminData();
    });
  });
}

function renderHealth(summary) {
  const health = summary.health || {};
  const requiredStepItems = Number(summary.required_response_count_per_reviewer || 0);
  const requiredComparisonItems = Number(summary.required_preference_response_count_per_reviewer || 0);
  const requiredItems = requiredStepItems + requiredComparisonItems;
  const metricCount = Number(summary.rubric_metric_count || 0);
  const assignedCount = requiredStepItems && metricCount ? requiredStepItems / (metricCount * 2) : 0;
  const expectedPerProp = assignedCount ? requiredItems / assignedCount : 0;
  $("healthList").innerHTML = `
    <div class="health-item">
      <b>Survey data</b>
      <span class="compact">Version ${escapeHtml(summary.version || "unknown")}; ${escapeHtml(summary.rubric_metric_count)} step metric; ${escapeHtml(requiredItems)} expected items per reviewer (${escapeHtml(requiredStepItems)} step scores + ${escapeHtml(requiredComparisonItems)} comparisons; ${escapeHtml(expectedPerProp)} per assigned proposition).</span>
    </div>
    <div class="health-item">
      <b>Missing Formalization B</b>
      ${countList(health.missing_new_method)}
    </div>
    <div class="health-item">
      <b>Missing Formalization A</b>
      ${countList(health.missing_leaneuclid)}
    </div>
    <div class="health-item">
      <b>Missing diagrams</b>
      ${countList(health.missing_diagrams)}
    </div>
    <div class="health-item">
      <b>Missing line-sentence mappings</b>
      ${countList((health.missing_mappings || []).map((item) => `${item.proposition_id}: ${item.methods.join(", ")}`))}
    </div>
  `;
}

function renderLeanStatus(lean) {
  const resources = lean.resources || {};
  const memory = resources.memory || {};
  const cgroup = resources.cgroup_memory || {};
  const load = resources.load_average || {};
  const fmt = (value, suffix = "") => value === undefined || value === null || value === "" ? "n/a" : `${value}${suffix}`;
  const cgroupValue = cgroup.current_mb === undefined || cgroup.current_mb === null
    ? "n/a"
    : cgroup.limit_mb === undefined || cgroup.limit_mb === null
      ? `${cgroup.current_mb} MB`
      : `${cgroup.current_mb} / ${cgroup.limit_mb} MB`;
  const cgroupHint = cgroup.source
    ? `Charged memory from ${cgroup.source}${cgroup.peak_mb ? `; peak ${cgroup.peak_mb} MB` : ""}`
    : "Job/container limit not available";
  const resourceCards = [
    ["Lean processes", fmt(resources.lean_process_count), "Active Lean server children"],
    ["Job/container memory", cgroupValue, cgroupHint],
    ["Process-tree PSS", fmt(resources.total_pss_mb, " MB"), "Server plus child processes, shared pages divided"],
    ["Lean PSS", fmt(resources.lean_pss_mb, " MB"), "Lean child processes, shared pages divided"],
    ["Summed RSS", fmt(resources.total_rss_mb, " MB"), "Diagnostic only; shared pages are overcounted"],
    ["Survey CPU", fmt(resources.total_cpu_percent, "%"), "Current server-owned CPU"],
    ["Load 1/5/15", `${fmt(load.one)} / ${fmt(load.five)} / ${fmt(load.fifteen)}`, `${fmt(resources.cpu_count)} CPU(s)`],
    ["Memory available", fmt(memory.available_mb, " MB"), `${fmt(memory.used_mb, " MB")} used on host`],
  ];
  $("leanStatus").innerHTML = `
    <div class="lean-item">
      <b>Active sessions</b>
      <span class="compact">${escapeHtml(lean.session_count)} Lean file sessions</span>
    </div>
    <div class="lean-item">
      <b>Proposition cache</b>
      <span class="compact">Global cap ${escapeHtml(lean.prop_cache_size)}; per-reviewer cache/warm-up cap ${escapeHtml(lean.prop_client_claim_cap || "n/a")}; pinned ${escapeHtml((lean.pinned_warm_prop_ids || []).join(", ") || "none")}; cached ${escapeHtml((lean.prop_cache_lru || []).join(", ") || "none")}</span>
    </div>
    <div class="lean-item">
      <b>Warm-up queue</b>
      <span class="compact">${escapeHtml(lean.warm_queue_size)} queued; ${escapeHtml(lean.warm_worker_count)} workers; latest request ${escapeHtml(lean.warm_latest_id || "none")}</span>
    </div>
    <div class="lean-item">
      <b>Recent warm-ups</b>
      ${expandableCountList("recentWarmups", (lean.warm_requests || []).map((req) => `${req.proposition_id || "unknown"}: ${req.status}`), "No warm-up requests")}
    </div>
    <div class="resource-card-grid">
      ${resourceCards.map(([label, value, hint]) => `
        <div class="resource-card">
          <span>${escapeHtml(label)}</span>
          <b>${escapeHtml(value)}</b>
          <em>${escapeHtml(hint)}</em>
        </div>
      `).join("")}
    </div>
    <div class="lean-item">
      <b>Top survey-owned processes by RSS</b>
      <div class="process-list">
        <span class="process-row process-head">
          <span>PID</span>
          <span>Command</span>
          <span>PSS</span>
          <span>RSS</span>
          <span>CPU</span>
        </span>
        ${(resources.top_processes || []).map((proc) => `
          <span class="process-row">
            <code>${escapeHtml(proc.pid)}</code>
            <span>${escapeHtml(proc.command)}</span>
            <span>${escapeHtml(fmt(proc.pss_mb, " MB"))}</span>
            <span>${escapeHtml(proc.rss_mb)} MB</span>
            <span>${escapeHtml(proc.cpu_percent)}%</span>
          </span>
        `).join("") || `<span class="compact">No process details available.</span>`}
      </div>
    </div>
  `;
  bindExpanders($("leanStatus"));
}

function renderProps(summary) {
  $("propRows").innerHTML = summary.propositions.map((prop) => `
    <tr>
      <td>
        <b>${escapeHtml(prop.display)}</b>
        <div class="compact">${escapeHtml(prop.title)}</div>
      </td>
      <td>${prop.ready ? pill("ready", "ready") : pill("missing pair", "missing")}</td>
      <td>${prop.in_assignment_pool ? pill("selected", "sample") : ""}</td>
      <td>${escapeHtml(prop.done_reviewers)} done / ${escapeHtml(prop.started_reviewers)} started</td>
      <td>${prop.diagram_available ? pill("available", "ready") : pill("missing", "warning")}</td>
      <td>${countList(prop.missing_mappings, "None")}</td>
    </tr>
  `).join("");
}

async function refreshSummary() {
  if (state.refreshInFlight.summary) return;
  state.refreshInFlight.summary = true;
  try {
    const summary = await api("/api/admin/summary");
    state.summary = summary;
    renderSummaryCards(summary);
    renderReviewers(summary);
    renderHealth(summary);
    renderProps(summary);
    renderExportFilterOptions();
    if (state.scores) renderScoreAnalytics();
  } finally {
    state.refreshInFlight.summary = false;
  }
}

async function refreshLeanStatus() {
  if (state.refreshInFlight.lean) return;
  state.refreshInFlight.lean = true;
  try {
    const lean = await api("/api/admin/lean/status");
    state.lean = lean;
    renderLeanStatus(lean);
  } finally {
    state.refreshInFlight.lean = false;
  }
}

async function refreshScores() {
  if (state.refreshInFlight.scores) return;
  state.refreshInFlight.scores = true;
  try {
    const scores = await api("/api/admin/scores");
    state.scores = scores;
    renderScoreAnalytics();
  } finally {
    state.refreshInFlight.scores = false;
  }
}

async function loadAdminData() {
  const [summary, lean, scores] = await Promise.all([
    api("/api/admin/summary"),
    api("/api/admin/lean/status"),
    api("/api/admin/scores"),
  ]);
  state.summary = summary;
  state.lean = lean;
  state.scores = scores;
  showAdmin();
  renderSummaryCards(summary);
  renderScoreAnalytics();
  renderReviewers(summary);
  renderHealth(summary);
  renderLeanStatus(lean);
  renderProps(summary);
  renderExportFilterOptions();
}

function stopLiveUpdates() {
  for (const timer of state.liveTimers) clearInterval(timer);
  state.liveTimers = [];
}

function startLiveUpdates() {
  stopLiveUpdates();
  if (document.hidden || $("adminApp").classList.contains("hidden")) return;
  state.liveTimers = [
    setInterval(() => refreshLeanStatus().catch(console.warn), 5000),
    setInterval(() => refreshSummary().catch(console.warn), 30000),
    setInterval(() => refreshScores().catch(console.warn), 60000),
  ];
}

function restartLiveUpdates() {
  if (document.hidden) {
    stopLiveUpdates();
    return;
  }
  startLiveUpdates();
  if (!$("adminApp").classList.contains("hidden")) {
    refreshLeanStatus().catch(console.warn);
    refreshSummary().catch(console.warn);
    refreshScores().catch(console.warn);
  }
}

async function checkSession() {
  const session = await api("/api/admin/session");
  if (!session.configured) {
    showLogin("Admin login is not configured on this server.");
    return;
  }
  if (!session.authenticated) {
    showLogin();
    return;
  }
  await loadAdminData();
  startLiveUpdates();
}

function bindEvents() {
  $("loginForm").addEventListener("submit", async (event) => {
    event.preventDefault();
    $("loginMessage").textContent = "";
    try {
      await api("/api/admin/login", {
        method: "POST",
        body: JSON.stringify({ password: $("adminPassword").value }),
      });
      $("adminPassword").value = "";
      await loadAdminData();
      startLiveUpdates();
    } catch (err) {
      $("loginMessage").textContent = err.message;
    }
  });

  $("logoutButton").addEventListener("click", async () => {
    stopLiveUpdates();
    await api("/api/admin/logout", { method: "POST", body: "{}" });
    showLogin();
  });

  $("refreshButton").addEventListener("click", async () => {
    await loadAdminData();
    startLiveUpdates();
  });

  $("reviewerStatusFilter").addEventListener("change", () => {
    state.scoreFilters.reviewerStatus = $("reviewerStatusFilter").value;
    renderScoreAnalytics();
  });

  $("reviewerFilter").addEventListener("change", () => {
    state.scoreFilters.reviewers = selectedValues($("reviewerFilter"));
    renderScoreAnalytics();
  });

  $("propFilter").addEventListener("change", () => {
    state.scoreFilters.propositions = selectedValues($("propFilter"));
    renderScoreAnalytics();
  });

  $("clearScoreFilters").addEventListener("click", () => {
    state.scoreFilters.reviewers = [];
    state.scoreFilters.propositions = [];
    renderScoreAnalytics();
  });

  $("exportReviewerStatusFilter").addEventListener("change", () => {
    state.exportFilters.reviewerStatus = $("exportReviewerStatusFilter").value;
    renderExportFilterOptions();
  });

  $("exportReviewerFilter").addEventListener("change", () => {
    state.exportFilters.reviewers = selectedValues($("exportReviewerFilter"));
    updateExportLinks();
  });

  $("clearExportFilters").addEventListener("click", () => {
    state.exportFilters.reviewers = [];
    renderExportFilterOptions();
  });

  document.querySelectorAll("a.download").forEach((link) => {
    link.addEventListener("click", async (event) => {
      event.preventDefault();
      try {
        await downloadEasternExport(link);
      } catch (err) {
        window.alert(`Export failed: ${err.message}`);
      }
    });
  });

  $("addReviewerForm").addEventListener("submit", async (event) => {
    event.preventDefault();
    const code = $("newReviewerCode").value.trim();
    if (!code) return;
    await api("/api/admin/reviewers", {
      method: "POST",
      body: JSON.stringify({ reviewer_code: code }),
    });
    $("newReviewerCode").value = "";
    await loadAdminData();
  });

  $("inviteReviewerForm").addEventListener("submit", async (event) => {
    event.preventDefault();
    const message = $("inviteMessage");
    message.textContent = "Sending personal survey link...";
    const email = $("inviteEmail").value.trim();
    const accessUrl = $("inviteAccessUrl").value.trim();
    try {
      const data = await api("/api/admin/reviewers/invite", {
        method: "POST",
        body: JSON.stringify({ email, access_url: accessUrl }),
      });
      $("inviteEmail").value = "";
      message.textContent = `Sent personal survey link to ${data.email}. Internal reviewer code: ${data.reviewer_code}`;
      await loadAdminData();
    } catch (err) {
      message.textContent = err.message;
    }
  });

  $("cancelWarmups").addEventListener("click", async () => {
    await api("/api/admin/lean/cancel-warmups", { method: "POST", body: "{}" });
    await loadAdminData();
  });

  $("clearLeanCache").addEventListener("click", async () => {
    await api("/api/admin/lean/clear-cache", { method: "POST", body: "{}" });
    await loadAdminData();
  });

  document.addEventListener("visibilitychange", restartLiveUpdates);
}

bindEvents();
checkSession().catch((err) => showLogin(err.message));
