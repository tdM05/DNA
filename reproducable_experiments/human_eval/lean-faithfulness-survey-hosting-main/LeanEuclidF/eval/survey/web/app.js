const state = {
  config: null,
  props: [],
  current: null,
  currentId: null,
  filter: "all",
  search: "",
  reviewerToken: localStorage.getItem("survey.reviewerToken") || "",
  progress: { responses: [], preferences: [], overall_notes: [], assigned_proposition_ids: [], review_target_count: 10 },
  draft: {},
  reviewStageByProp: JSON.parse(localStorage.getItem("survey.reviewStageByProp") || "{}"),
  completedNoticePropId: "",
  hoverStandard: {},
  warm: {},
  warmRequests: {},
  sidebarCollapsed: localStorage.getItem("survey.sidebarCollapsed") === "true",
  leanCollapsed: localStorage.getItem("survey.leanCollapsed") === "true",
  comparisonCollapsed: {
    reading: true,
    code: true,
  },
  codeWrap: {
    leaneuclid: localStorage.getItem("survey.codeWrap.leaneuclid") ?? localStorage.getItem("survey.codeWrap") ?? "true",
    new_method: localStorage.getItem("survey.codeWrap.new_method") ?? localStorage.getItem("survey.codeWrap") ?? "true",
  },
  activeLine: null,
  activeLeanState: null,
  activeLeanData: null,
  leanStateKey: 0,
  leanStates: {},
  leanStateCache: {},
  leanHoverCache: {},
  definitionCache: {},
  activeFiles: {},
  openFiles: {},
  externalFiles: {},
  codeScroll: {},
  currentWarmKey: "",
  navSeq: 0,
  tutorial: {
    version: "2",
    active: false,
    completed: false,
    step: 0,
    target: null,
    leanStateDemoKey: "",
    origin: null,
  },
};

let leanHoverTimer = null;
let leanHoverPending = null;
let leanHoverHideTimer = null;
let leanHoverKey = "";
let sourceHoverLine = null;
let sourceClickableLine = null;
let ctrlClickAffordance = null;
let activeMappingMethod = "";
let activeMappingIds = [];
let lastCodePointer = null;
let ctrlClickTimer = null;
let ctrlClickKey = "";
let leanStateController = null;
let leanStateSeq = 0;
let leanCursorQueryTimer = null;
let autosaveTimer = null;
let autosaveSeq = 0;
let propFetchController = null;
let methodStageResizeObserver = null;

const $ = (id) => document.getElementById(id);

function escapeHtml(text) {
  return String(text ?? "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;");
}

function encodeAttrJson(value) {
  return encodeURIComponent(JSON.stringify(value ?? null));
}

async function api(path, opts = {}) {
  const res = await fetch(path, {
    headers: { "Content-Type": "application/json", ...(opts.headers || {}) },
    ...opts,
  });
  if (!res.ok) {
    let msg = `${res.status} ${res.statusText}`;
    try {
      const data = await res.json();
      msg = data.error || msg;
    } catch (_) {}
    throw new Error(msg);
  }
  return res.json();
}

const leanControllers = new Set();
const leanPageClientId = `lc_${Date.now().toString(36)}_${Math.random().toString(36).slice(2, 10)}`;

function leanClientId() {
  return leanPageClientId;
}

function reviewerToken() {
  return String(state.reviewerToken || "").trim();
}

function isAbortError(err) {
  return err?.name === "AbortError";
}

function isStaleLeanError(err) {
  return isAbortError(err) || String(err?.message || "").includes("stale Lean");
}

function abortLeanRequests() {
  if (leanStateController) {
    leanStateController.abort();
    leanStateController = null;
  }
  leanStateSeq += 1;
  for (const controller of leanControllers) controller.abort();
  leanControllers.clear();
  clearTimeout(leanCursorQueryTimer);
  clearTimeout(leanHoverTimer);
  clearTimeout(leanHoverHideTimer);
  leanHoverPending = null;
  leanHoverKey = "";
  hideLeanInfoPopup();
  hideLineMappingPopup();
}

async function leanApi(path, payload) {
  const controller = new AbortController();
  leanControllers.add(controller);
  try {
    return await api(path, {
      method: "POST",
      signal: controller.signal,
      body: JSON.stringify({ ...(payload || {}), client_id: leanClientId() }),
    });
  } finally {
    leanControllers.delete(controller);
  }
}

function setGateMessage(text, kind = "") {
  const el = $("gateMessage");
  if (!el) return;
  el.textContent = text;
  el.className = `gate-message ${kind}`.trim();
}

function inviteTokenFromHash() {
  const hash = window.location.hash || "";
  if (!hash.startsWith("#invite=")) return "";
  try {
    return decodeURIComponent(hash.slice("#invite=".length).split("&", 1)[0]);
  } catch (_) {
    return hash.slice("#invite=".length).split("&", 1)[0];
  }
}

function clearInviteHash() {
  if (!window.location.hash.startsWith("#invite=")) return;
  history.replaceState(null, "", `${location.pathname}${location.search}`);
}

async function reviewerTokenExists(token) {
  const clean = String(token || "").trim();
  if (!clean) return false;
  try {
    const data = await api(`/api/invites/${encodeURIComponent(clean)}`);
    return Boolean(data.ok);
  } catch (_) {
    return false;
  }
}

async function requestReviewerLink(email) {
  return api("/api/reviewer-links", {
    method: "POST",
    body: JSON.stringify({ email: String(email || "").trim() }),
  });
}

function tutorialSteps() {
  return [
    {
      selector: null,
      title: "Use your personal survey link",
      body: "This page is for judging how faithfully Lean formalizations follow the textbook proposition and proof. Your personal survey link resumes your progress; responses are stored under that link, not shown with your email.",
    },
    {
      selector: "#propList",
      scroll: false,
      prepare: () => setSidebarCollapsed(false),
      title: "Find assigned propositions",
      body: "Your link assigns 10 propositions to score. Assigned propositions have a stronger left accent and show Not started, In progress, or Done. Lighter Browse only propositions can still be inspected, but scoring is disabled for them. Use the small arrow in this sidebar header to collapse the list when you want more workspace.",
    },
    {
      selector: ".prop-nav",
      fallbackSelector: ".topbar",
      prepare: () => prepareMethodStageTutorialStep(),
      title: "Move through review questions",
      body: "Within a proposition, use Next question after finishing the current question to move from Formalization A to Formalization B, then to the Comparison page. Prev question returns to the previous question.",
    },
    {
      selector: ".reading-grid",
      prepare: () => prepareMethodStageTutorialStep(),
      title: "Start from the textbook",
      body: "Read the natural-language proposition and proof first. Use the diagram when available, and click textbook references to inspect the cited proposition, postulate, definition, or common notion.",
    },
    {
      selector: ".formalization-grid",
      prepare: () => prepareMethodStageTutorialStep(),
      title: "Review one formalization",
      body: "Score one formalization at a time. During Formalization A or B, the textbook and the active Lean formalization are shown side by side so you can focus on one proof.",
    },
    {
      selector: ".code-map-badge.map-single, .code-map-badge.map-start",
      fallbackSelector: ".formalization-grid",
      prepare: () => prepareMethodStageTutorialStep(),
      title: "Use sentence-mapping badges",
      body: "Hover a badge beside Lean code to highlight the textbook sentence or sentence range that the code is intended to formalize. These AI-generated mappings are aids for orientation, not ground truth.",
    },
    {
      selector: ".book-dependency-token",
      fallbackSelector: ".formalization-grid",
      prepare: () => prepareMethodStageTutorialStep(),
      title: "Inspect dependencies in code",
      body: "Mildly highlighted Lean names are in-book dependencies such as propositions, postulates, and helper lemmas. Hover Lean terms for type information, and Ctrl-click or Cmd-click clickable names to jump to their definitions when available.",
    },
    {
      selector: "#leanPanel",
      prepare: () => prepareLeanStateTutorialStep(),
      title: "Inspect Lean state",
      body: "Click a Lean line when you need more evidence. The Lean state panel shows goals, hypotheses, diagnostics, and messages for the selected line, similar to VS Code InfoView.",
    },
    {
      selector: "#metricCards .metric-card",
      fallbackSelector: "#metricCards",
      prepare: () => prepareScoringTutorialStep(),
      title: "Score step fidelity",
      body: "Each formalization is scored independently on Step Fidelity. Select the rubric row from 0 to 5 that best describes how faithfully the active proof captures the textbook's mathematical steps.",
    },
    {
      selector: ".preference-cards",
      fallbackSelector: "#metricCards",
      prepare: () => prepareComparisonTutorialStep(),
      title: "Compare the two formalizations",
      body: "After both formalizations are scored, answer three A-versus-B preference questions using the seven-circle scales. On the comparison page, the textbook, diagram, and code panels start collapsed so the questions are visible first; expand them when needed.",
    },
    {
      selector: "#nextAssignedProp",
      scroll: false,
      prepare: () => setSidebarCollapsed(true),
      title: "Jump to the next proposition",
      body: "After finishing a proposition, use Next proposition to move to another assigned proposition. It cycles through your 10 review items, shows your progress as x/10 done, and is highlighted when the current proposition is complete.",
    },
    {
      selector: "#saveStatus",
      fallbackSelector: ".topbar",
      title: "Autosave handles progress",
      body: "Step scores and comparison choices are saved automatically. A proposition becomes Done after both formalizations have scores and all three comparison questions are answered.",
    },
    {
      selector: "#tutorialButton",
      title: "Reopen this tutorial anytime",
      body: "Use the Tutorial button whenever you want to revisit the reviewing workflow. Reopening the tutorial never changes your saved responses.",
    },
  ];
}

async function loadTutorialStatus() {
  if (!reviewerToken()) return false;
  try {
    const data = await api(`/api/tutorial-token/${encodeURIComponent(reviewerToken())}`);
    state.tutorial.completed = Boolean(data.completed);
    return state.tutorial.completed;
  } catch (err) {
    console.warn("Tutorial status unavailable", err);
    return false;
  }
}

async function markTutorialComplete() {
  if (!reviewerToken() || state.tutorial.completed) return;
  state.tutorial.completed = true;
  try {
    await api("/api/tutorial", {
      method: "POST",
      body: JSON.stringify({
        reviewer_token: reviewerToken(),
        tutorial_version: state.tutorial.version,
      }),
    });
  } catch (err) {
    state.tutorial.completed = false;
    console.warn("Tutorial completion save failed", err);
  }
}

function ready(prop) {
  return prop.methodAvailability?.leaneuclid && prop.methodAvailability?.new_method;
}

function responseKey(propId, methodId, metricId) {
  return `${propId}::${methodId}::${metricId}`;
}

function existingResponse(propId, methodId, metricId) {
  return state.progress.responses.find(
    (r) => r.proposition_id === propId && r.method_id === methodId && r.metric_id === metricId
  );
}

function getScore(propId, methodId, metricId) {
  const key = responseKey(propId, methodId, metricId);
  if (state.draft[key]?.score !== undefined) return state.draft[key].score;
  const found = existingResponse(propId, methodId, metricId);
  return found ? found.score : null;
}

function getNote(propId, methodId, metricId) {
  const key = responseKey(propId, methodId, metricId);
  if (state.draft[key]?.note !== undefined) return state.draft[key].note;
  const found = existingResponse(propId, methodId, metricId);
  return found ? found.note : "";
}

function getOverallNote(propId) {
  const key = `${propId}::overall`;
  if (state.draft[key] !== undefined) return state.draft[key];
  const found = state.progress.overall_notes.find((n) => n.proposition_id === propId);
  return found ? found.note : "";
}

function preferenceKey(propId, questionId) {
  return `${propId}::preference::${questionId}`;
}

function canonicalPreferenceChoice(prop, uiChoice) {
  if (uiChoice === null || uiChoice === undefined) return uiChoice;
  const value = Number(uiChoice);
  if (!Number.isFinite(value) || value === 0) return value;
  return methodIdForSlot("A", prop) === "leaneuclid" ? value : -value;
}

function uiPreferenceChoice(prop, canonicalChoice) {
  if (canonicalChoice === null || canonicalChoice === undefined) return canonicalChoice;
  const value = Number(canonicalChoice);
  if (!Number.isFinite(value) || value === 0) return value;
  return methodIdForSlot("A", prop) === "leaneuclid" ? value : -value;
}

function existingPreference(propId, questionId) {
  return (state.progress.preferences || []).find(
    (r) => r.proposition_id === propId && r.question_id === questionId
  );
}

function getPreference(propId, questionId) {
  const key = preferenceKey(propId, questionId);
  if (state.draft[key]?.choice !== undefined) return state.draft[key].choice;
  const found = existingPreference(propId, questionId);
  return found ? found.choice : null;
}

function metricList() {
  return state.config?.rubric.metrics || [];
}

function preferenceQuestions() {
  return state.config?.preference_questions?.questions || [];
}

function methodScored(propId, methodId) {
  return metricList().every((m) => existingResponse(propId, methodId, m.id));
}

function methodDraftOrSavedScored(propId, methodId) {
  return metricList().every((m) => getScore(propId, methodId, m.id) !== null);
}

function preferencesComplete(propId) {
  return preferenceQuestions().every((q) => existingPreference(propId, q.id));
}

function preferencesDraftOrSavedComplete(propId) {
  return preferenceQuestions().every((q) => getPreference(propId, q.id) !== null);
}

function isDone(propId) {
  if (!isAssigned(propId)) return false;
  const methods = ["leaneuclid", "new_method"];
  return methods.every((methodId) => methodScored(propId, methodId)) && preferencesComplete(propId);
}

function isAssigned(propId) {
  return (state.progress.assigned_proposition_ids || []).includes(propId);
}

function assignedProps() {
  const assigned = new Set(state.progress.assigned_proposition_ids || []);
  return state.props.filter((p) => assigned.has(p.id));
}

function hasReviewInput(propId) {
  if (state.progress.responses.some((r) => r.proposition_id === propId)) return true;
  if ((state.progress.preferences || []).some((r) => r.proposition_id === propId)) return true;
  if (state.progress.overall_notes.some((n) => n.proposition_id === propId && String(n.note || "").trim())) return true;
  const prefix = `${propId}::`;
  return Object.entries(state.draft).some(([key, value]) => {
    if (!key.startsWith(prefix)) return false;
    if (key.endsWith("::overall")) return Boolean(String(value || "").trim());
    if (key.includes("::preference::")) return value?.choice !== undefined;
    return value?.score !== undefined || Boolean(String(value?.note || "").trim());
  });
}

function reviewStatus(propId) {
  if (!isAssigned(propId)) return { id: "browse_only", label: "Browse only" };
  if (isDone(propId)) return { id: "done", label: "Done" };
  if (hasReviewInput(propId)) return { id: "in_progress", label: "In progress" };
  return { id: "not_started", label: "Not started" };
}

function assignedProgressText() {
  const assigned = assignedProps();
  const done = assigned.filter((p) => isDone(p.id)).length;
  const target = state.progress.review_target_count || assigned.length;
  return `${done}/${target} done`;
}

function allAssignedPropsDone() {
  const assigned = assignedProps();
  return assigned.length > 0 && assigned.every((p) => isDone(p.id));
}

function canReviewProp(prop) {
  const availability = prop?.methods
    ? { leaneuclid: prop.methods.leaneuclid?.available, new_method: prop.methods.new_method?.available }
    : prop?.methodAvailability;
  return Boolean(prop && isAssigned(prop.id) && availability?.leaneuclid && availability?.new_method);
}

function renderPropList() {
  const list = $("propList");
  const q = state.search.toLowerCase();
  const items = state.props.filter((p) => {
    const status = reviewStatus(p.id);
    if (state.filter === "assigned" && !isAssigned(p.id)) return false;
    if (state.filter !== "all" && state.filter !== "assigned" && status.id !== state.filter) return false;
    if (q && !`${p.number} ${p.display} ${p.title}`.toLowerCase().includes(q)) return false;
    return true;
  });
  if ($("nextAssignedProp")) $("nextAssignedProp").textContent = `Next proposition (${assignedProgressText()})`;
  list.innerHTML = items.map((p) => `
    <button class="prop-item ${p.id === state.currentId ? "active" : ""} ${isAssigned(p.id) ? "assigned" : "browse-only"}" data-prop="${p.id}">
      <span class="num">Prop ${p.number}<span class="badge ${reviewStatus(p.id).id}">${reviewStatus(p.id).label}</span></span>
      <span class="title">${escapeHtml(p.title)}</span>
    </button>
  `).join("");
  list.querySelectorAll("[data-prop]").forEach((btn) => {
    btn.addEventListener("click", () => selectProp(btn.dataset.prop));
  });
  keepActivePropInView();
}

function keepActivePropInView() {
  if (state.sidebarCollapsed) return;
  const sidebar = $("sidebar");
  const active = $("propList")?.querySelector(".prop-item.active");
  if (!sidebar || !active) return;
  requestAnimationFrame(() => {
    const sidebarRect = sidebar.getBoundingClientRect();
    const activeRect = active.getBoundingClientRect();
    const stickyHeader = sidebar.querySelector(".brand");
    const topPadding = (stickyHeader?.getBoundingClientRect().height || 0) + 16;
    const bottomPadding = 18;
    if (activeRect.top < sidebarRect.top + topPadding) {
      sidebar.scrollTop -= (sidebarRect.top + topPadding) - activeRect.top;
    } else if (activeRect.bottom > sidebarRect.bottom - bottomPadding) {
      sidebar.scrollTop += activeRect.bottom - (sidebarRect.bottom - bottomPadding);
    }
  });
}

function isUsableTutorialTarget(el) {
  if (!el) return false;
  const style = window.getComputedStyle(el);
  if (style.display === "none" || style.visibility === "hidden" || Number(style.opacity) === 0) return false;
  const rects = Array.from(el.getClientRects()).filter((rect) => rect.width > 0 && rect.height > 0);
  return rects.length > 0;
}

function firstTutorialTarget(selector) {
  return Array.from(document.querySelectorAll(selector)).find(isUsableTutorialTarget) || null;
}

function tutorialTarget(step) {
  if (!step.selector) return null;
  return firstTutorialTarget(step.selector) || (step.fallbackSelector ? firstTutorialTarget(step.fallbackSelector) : null);
}

function prepareMethodStageTutorialStep(preferredStage = "A") {
  setSidebarCollapsed(true);
  if (!state.current || stageForProp(state.current) !== "compare") return;
  setStage(state.current, preferredStage);
}

function prepareLeanStateTutorialStep() {
  prepareMethodStageTutorialStep();
  setLeanCollapsed(false);
  requestAnimationFrame(() => {
    const prop = state.current;
    const methodId = stageMethodId(prop);
    if (!prop || !methodId) return;
    const target = firstVisibleCodeLine(methodId);
    if (!target || !state.current) return;
    const filePath = target.dataset.file;
    const line = Number(target.dataset.line);
    const column = codeLineText(target).length;
    target.scrollIntoView({ block: "center", inline: "nearest", behavior: "smooth" });
    const demoKey = `${prop.id}:${methodId}:${filePath}:${line}:${column}`;
    if (state.tutorial.leanStateDemoKey === demoKey) return;
    state.tutorial.leanStateDemoKey = demoKey;
    inspectLeanLine(prop.id, methodId, filePath, line, target, column, { navSeq: state.navSeq });
  });
}

function prepareComparisonTutorialStep() {
  setSidebarCollapsed(true);
  if (!state.current || stageForProp(state.current) === "compare") return;
  setStage(state.current, "compare");
}

function prepareScoringTutorialStep() {
  prepareMethodStageTutorialStep();
}

function positionTutorial() {
  if (!state.tutorial.active) return;
  const ring = $("tutorialRing");
  const card = $("tutorialCard");
  const target = state.tutorial.target;
  if (!ring || !card) return;

  if (!target) {
    ring.classList.add("hidden");
    const cardWidth = Math.min(420, window.innerWidth - 24);
    card.style.width = `${cardWidth}px`;
    card.style.left = `${Math.max(12, (window.innerWidth - cardWidth) / 2)}px`;
    card.style.top = `${Math.max(12, (window.innerHeight - (card.offsetHeight || 230)) / 2)}px`;
    return;
  }
  ring.classList.remove("hidden");

  const rect = target.getBoundingClientRect();
  const margin = 8;
  const ringLeft = Math.max(8, rect.left - margin);
  const ringTop = Math.max(8, rect.top - margin);
  const ringWidth = Math.min(window.innerWidth - ringLeft - 8, rect.width + margin * 2);
  const ringHeight = Math.min(window.innerHeight - ringTop - 8, rect.height + margin * 2);
  ring.style.left = `${ringLeft}px`;
  ring.style.top = `${ringTop}px`;
  ring.style.width = `${Math.max(44, ringWidth)}px`;
  ring.style.height = `${Math.max(32, ringHeight)}px`;

  const cardWidth = Math.min(420, window.innerWidth - 24);
  const cardHeight = card.offsetHeight || 230;
  let left = rect.right + 18;
  if (left + cardWidth > window.innerWidth - 12) left = rect.left - cardWidth - 18;
  if (left < 12) left = Math.min(window.innerWidth - cardWidth - 12, 12);
  let top = rect.top;
  if (top + cardHeight > window.innerHeight - 12) top = window.innerHeight - cardHeight - 12;
  if (top < 12) top = 12;
  card.style.left = `${left}px`;
  card.style.top = `${top}px`;
  card.style.width = `${cardWidth}px`;
}

function renderTutorialStep() {
  const steps = tutorialSteps();
  const step = steps[state.tutorial.step];
  if (!step) return closeTutorial(true);
  step.prepare?.();

  requestAnimationFrame(() => {
    const target = tutorialTarget(step) || $("app");
    state.tutorial.target = step.selector ? target : null;
    if (state.tutorial.target && step.scroll !== false) {
      state.tutorial.target.scrollIntoView?.({ block: "center", inline: "center", behavior: "auto" });
    }
    setTimeout(() => {
      $("tutorialStepCount").textContent = `Step ${state.tutorial.step + 1} of ${steps.length}`;
      $("tutorialTitle").textContent = step.title;
      $("tutorialBody").textContent = step.body;
      $("tutorialBack").disabled = state.tutorial.step === 0;
      $("tutorialNext").textContent = state.tutorial.step === steps.length - 1 ? "Done" : "Next";
      positionTutorial();
    }, 120);
  });
}

function openTutorial(manual = false) {
  state.tutorial.leanStateDemoKey = "";
  if (!state.current && state.props[0]) {
    selectProp(state.currentId || state.props[0].id).then(() => openTutorial(manual));
    return;
  }
  state.tutorial.origin = state.current
    ? { propId: state.current.id, stage: stageForProp(state.current) }
    : null;
  state.tutorial.active = true;
  state.tutorial.step = 0;
  $("tutorialOverlay").classList.remove("hidden");
  renderTutorialStep();
}

function restoreTutorialOrigin() {
  const origin = state.tutorial.origin;
  state.tutorial.origin = null;
  if (!origin?.propId) return;
  if (state.current?.id === origin.propId) {
    setStageForProp(state.current, origin.stage);
    renderCurrent();
    return;
  }
  selectProp(origin.propId).then(() => {
    if (!state.current || state.current.id !== origin.propId) return;
    setStageForProp(state.current, origin.stage);
    renderCurrent();
  });
}

function closeTutorial(markComplete = false) {
  state.tutorial.active = false;
  state.tutorial.target = null;
  $("tutorialOverlay")?.classList.add("hidden");
  restoreTutorialOrigin();
  if (markComplete) markTutorialComplete();
}

function nextTutorialStep() {
  const steps = tutorialSteps();
  if (state.tutorial.step >= steps.length - 1) {
    closeTutorial(true);
    return;
  }
  state.tutorial.step += 1;
  renderTutorialStep();
}

function previousTutorialStep() {
  if (state.tutorial.step <= 0) return;
  state.tutorial.step -= 1;
  renderTutorialStep();
}

function texMathToDisplay(text) {
  return String(text || "")
    .replaceAll("\\triangle", "△")
    .replaceAll("\\angle", "∠")
    .replaceAll("\\cong", "≅")
    .replaceAll("\\neq", "≠")
    .replaceAll("\\ne", "≠")
    .replaceAll("\\leq", "≤")
    .replaceAll("\\geq", "≥")
    .replaceAll("\\lt", "<")
    .replaceAll("\\gt", ">")
    .replaceAll("\\cdot", "·")
    .replaceAll("\\times", "×")
    .replaceAll("\\parallel", "∥")
    .replaceAll("\\perp", "⊥")
    .replaceAll("\\sim", "∼")
    .replaceAll("\\simeq", "≃")
    .replaceAll("\\left", "")
    .replaceAll("\\right", "")
    .replaceAll("\\,", " ")
    .replaceAll("~", " ")
    .replace(/[{}]/g, "")
    .replace(/\s+/g, " ")
    .trim();
}

function displayReferenceLabel(ref) {
  if (!ref) return "";
  if (ref.kind === "proposition") return `Prop. ${ref.book}.${ref.number}`;
  if (ref.kind === "post") return `Post. ${ref.number}`;
  if (ref.kind === "cn") return `C.N. ${ref.number}`;
  if (ref.kind === "def") return `Def. ${ref.book}.${ref.number}`;
  return ref.raw || "";
}

function parseTextReference(raw) {
  const clean = String(raw || "").replaceAll("~", " ").replace(/\s+/g, " ").trim();
  let match = clean.match(/^Prop\.?\s*(\d+)\.(\d+)$/i);
  if (match) {
    const book = Number(match[1]);
    const number = Number(match[2]);
    return { kind: "proposition", book, number, propId: `book${book}_prop${String(number).padStart(2, "0")}`, raw: clean };
  }
  match = clean.match(/^Post\.?\s*(?:(\d+)\.)?(\d+)$/i);
  if (match) return { kind: "post", number: Number(match[2]), refId: `post:${Number(match[2])}`, raw: clean };
  match = clean.match(/^C\.?\s*N\.?\s*(\d+)$/i);
  if (match) return { kind: "cn", number: Number(match[1]), refId: `cn:${Number(match[1])}`, raw: clean };
  match = clean.match(/^Def\.?\s*(?:(\d+)\.)?(\d+)$/i);
  if (match) {
    const book = Number(match[1] || 1);
    const number = Number(match[2]);
    return { kind: "def", book, number, refId: `def:${number}`, raw: clean };
  }
  return null;
}

function renderEuclidText(text) {
  const raw = String(text || "");
  let html = "";
  let pos = 0;
  const pattern = /\$([^$]+)\$|\[([^\]]+)\]/g;
  for (const match of raw.matchAll(pattern)) {
    html += escapeHtml(raw.slice(pos, match.index));
    if (match[1] !== undefined) {
      html += `<span class="math-inline">${escapeHtml(texMathToDisplay(match[1]))}</span>`;
    } else {
      const ref = parseTextReference(match[2]);
      if (ref?.kind === "proposition") {
        html += `<button class="text-ref text-ref-prop" type="button" data-prop-ref="${escapeHtml(ref.propId)}" title="Open ${escapeHtml(displayReferenceLabel(ref))}">[${escapeHtml(displayReferenceLabel(ref))}]</button>`;
      } else if (ref?.refId && state.config?.references?.[ref.refId]) {
        html += `<button class="text-ref" type="button" data-ref-id="${escapeHtml(ref.refId)}" title="Show ${escapeHtml(displayReferenceLabel(ref))}">[${escapeHtml(displayReferenceLabel(ref))}]</button>`;
      } else {
        html += `[${escapeHtml(match[2])}]`;
      }
    }
    pos = match.index + match[0].length;
  }
  html += escapeHtml(raw.slice(pos));
  return html;
}

function renderText(prop) {
  const { propositionSentences, proofSentences } = partitionTextSentences(prop);
  $("nlText").innerHTML = `
    <section class="nl-section">
      <h4>Proposition</h4>
      <div class="nl-raw">${renderTextWithSentenceSpans(prop.proposition_text || "", propositionSentences)}</div>
    </section>
    <section class="nl-section">
      <h4>Proof</h4>
      <div class="nl-raw">${renderTextWithSentenceSpans(prop.proof_text || "", proofSentences)}</div>
    </section>
  `;
}

function partitionTextSentences(prop) {
  const sentences = prop.text_sentences || [];
  const propositionTarget = normalizeForSentenceMatch(prop.proposition_text || sentences[0]?.text || "");
  if (!propositionTarget) return { propositionSentences: [], proofSentences: sentences };
  const propositionSentences = [];
  let matched = false;
  for (const sentence of sentences) {
    propositionSentences.push(sentence);
    if (normalizeForSentenceMatch(propositionSentences.map((item) => item.text).join(" ")) === propositionTarget) {
      matched = true;
      break;
    }
  }
  if (!matched) {
    return {
      propositionSentences: sentences.slice(0, 1),
      proofSentences: sentences.slice(1),
    };
  }
  return {
    propositionSentences,
    proofSentences: sentences.slice(propositionSentences.length),
  };
}

function normalizedTextMap(raw) {
  const chars = [];
  const starts = [];
  const ends = [];
  let i = 0;
  while (i < raw.length) {
    if (/\s/.test(raw[i])) {
      const start = i;
      while (i < raw.length && /\s/.test(raw[i])) i += 1;
      if (chars.length && chars[chars.length - 1] !== " ") {
        chars.push(" ");
        starts.push(start);
        ends.push(i);
      }
      continue;
    }
    chars.push(raw[i]);
    starts.push(i);
    ends.push(i + 1);
    i += 1;
  }
  if (chars[chars.length - 1] === " ") {
    chars.pop();
    starts.pop();
    ends.pop();
  }
  return { text: chars.join(""), starts, ends };
}

function normalizeForSentenceMatch(text) {
  return String(text || "").replace(/\s+/g, " ").trim();
}

function renderTextWithSentenceSpans(raw, sentences) {
  if (!raw || !sentences?.length) return renderEuclidText(raw);
  const mapped = normalizedTextMap(raw);
  let searchFrom = 0;
  let rawPos = 0;
  let html = "";
  for (const sentence of sentences) {
    const needle = normalizeForSentenceMatch(sentence.text);
    if (!needle) continue;
    const idx = mapped.text.indexOf(needle, searchFrom);
    if (idx < 0) continue;
    const rawStart = mapped.starts[idx];
    const rawEnd = mapped.ends[idx + needle.length - 1];
    if (rawStart < rawPos || rawEnd < rawStart) continue;
    html += renderEuclidText(raw.slice(rawPos, rawStart));
    html += `<span class="nl-sentence" data-sentence-id="${escapeHtml(String(sentence.id || "").toLowerCase())}">${renderEuclidText(raw.slice(rawStart, rawEnd))}</span>`;
    rawPos = rawEnd;
    searchFrom = idx + needle.length;
  }
  html += renderEuclidText(raw.slice(rawPos));
  return html || renderEuclidText(raw);
}

function sentenceLookup(prop = state.current) {
  return Object.fromEntries((prop?.text_sentences || []).map((sentence) => [sentence.id, sentence]));
}

function lineMappingsForLine(method, filePath, lineNumber) {
  return (method?.line_text_mappings || []).filter((mapping) =>
    (mapping.code_ranges || []).some((range) =>
      range.file === filePath &&
      Number(range.start_line) <= Number(lineNumber) &&
      Number(lineNumber) <= Number(range.end_line)
    )
  );
}

function lineMappingSegmentsForLine(method, filePath, lineNumber) {
  const segments = [];
  for (const mapping of method?.line_text_mappings || []) {
    for (const range of mapping.code_ranges || []) {
      const start = Number(range.start_line);
      const end = Number(range.end_line);
      if (range.file !== filePath || start > Number(lineNumber) || Number(lineNumber) > end) continue;
      const position = start === end
        ? "single"
        : Number(lineNumber) === start
          ? "start"
          : Number(lineNumber) === end
            ? "end"
            : "middle";
      segments.push({ mapping, position });
    }
  }
  return segments;
}

function sentenceLabel(sentenceIds) {
  const nums = [...new Set((sentenceIds || []).map((id) => Number(String(id).replace(/^s/i, ""))).filter(Boolean))].sort((a, b) => a - b);
  if (!nums.length) return "";
  const ranges = [];
  let start = nums[0];
  let prev = nums[0];
  for (const n of nums.slice(1)) {
    if (n === prev + 1) {
      prev = n;
      continue;
    }
    ranges.push(start === prev ? `S${start}` : `S${start}-${prev}`);
    start = prev = n;
  }
  ranges.push(start === prev ? `S${start}` : `S${start}-${prev}`);
  return ranges.join(", ");
}

function mappingBadgeHtml(method, filePath, lineNumber) {
  const segments = lineMappingSegmentsForLine(method, filePath, lineNumber);
  if (!segments.length) return `<span class="map-cell"></span>`;
  return `
    <span class="map-cell">
      ${segments.map(({ mapping, position }) => {
        const label = position === "start" || position === "single" ? sentenceLabel(mapping.sentence_ids || []) : "";
        return `
          <span class="code-map-badge map-${position}"
            data-mapping-ids="${encodeAttrJson([mapping.id])}"
            title="Show textbook sentence mapping">
            ${label ? escapeHtml(label) : "&nbsp;"}
          </span>
        `;
      }).join("")}
    </span>
  `;
}

function renderDiagram(prop) {
  if (prop.diagram.available) {
    $("diagramBox").innerHTML = `<img src="${prop.diagram.path}" alt="Diagram for proposition ${prop.number}">`;
  } else {
    $("diagramBox").innerHTML = `<p class="subtle">No diagram available.</p>`;
  }
}

function textReferencePopup() {
  let el = $("textReferencePopup");
  if (!el) {
    el = document.createElement("div");
    el.id = "textReferencePopup";
    el.className = "text-ref-popup hidden";
    document.body.appendChild(el);
  }
  return el;
}

function positionTextReferencePopup(anchor) {
  const popup = textReferencePopup();
  const rect = anchor.getBoundingClientRect();
  const width = Math.min(460, window.innerWidth - 24);
  const height = popup.offsetHeight || 180;
  popup.style.maxWidth = `${width}px`;
  popup.style.left = `${Math.min(window.innerWidth - width - 12, Math.max(12, rect.left))}px`;
  popup.style.top = `${Math.min(window.innerHeight - height - 12, rect.bottom + 8)}px`;
}

function showTextReference(refId, anchor) {
  const ref = state.config?.references?.[refId];
  if (!ref) return;
  const popup = textReferencePopup();
  popup.classList.remove("hidden");
  popup.innerHTML = `
    <div class="text-ref-popup-head">
      <div>
        <p class="eyebrow">${escapeHtml(ref.kind === "cn" ? "Common notion" : ref.kind === "post" ? "Postulate" : "Definition")}</p>
        <h4>${escapeHtml(ref.label)}</h4>
      </div>
      <button class="icon-button text-ref-close" type="button" title="Close reference" aria-label="Close reference">×</button>
    </div>
    <div class="text-ref-popup-body">${renderEuclidText(ref.text)}</div>
  `;
  popup.querySelector(".text-ref-close")?.addEventListener("click", hideTextReferencePopup);
  positionTextReferencePopup(anchor);
}

function hideTextReferencePopup() {
  textReferencePopup().classList.add("hidden");
}

function shortFileName(path) {
  const parts = String(path || "").split("/");
  return parts[parts.length - 1] || path;
}

function stableHash(text) {
  let hash = 0;
  for (const ch of String(text || "")) {
    hash = ((hash << 5) - hash + ch.charCodeAt(0)) | 0;
  }
  return Math.abs(hash);
}

function methodSlotOrder(prop = state.current) {
  const swapped = stableHash(prop?.id || "") % 2 === 1;
  return swapped
    ? [{ slot: "A", methodId: "new_method" }, { slot: "B", methodId: "leaneuclid" }]
    : [{ slot: "A", methodId: "leaneuclid" }, { slot: "B", methodId: "new_method" }];
}

function methodSlotFor(methodId, prop = state.current) {
  return methodSlotOrder(prop).find((item) => item.methodId === methodId)?.slot || (methodId === "leaneuclid" ? "A" : "B");
}

function methodIdForSlot(slot, prop = state.current) {
  return methodSlotOrder(prop).find((item) => item.slot === slot)?.methodId || (slot === "A" ? "leaneuclid" : "new_method");
}

function methodDisplayLabel(methodId, prop = state.current) {
  return `Formalization ${methodSlotFor(methodId, prop)}`;
}

function codeContainer(methodId) {
  return methodSlotFor(methodId) === "A" ? $("methodACode") : $("methodBCode");
}

function stageForProp(prop = state.current) {
  if (!prop) return "A";
  return state.reviewStageByProp[prop.id] || recommendedStage(prop);
}

function setStageForProp(prop, stage) {
  if (!prop) return;
  const clean = ["A", "B", "compare"].includes(stage) ? stage : "A";
  state.reviewStageByProp[prop.id] = clean;
  localStorage.setItem("survey.reviewStageByProp", JSON.stringify(state.reviewStageByProp));
  if (clean === "compare") {
    state.comparisonCollapsed.reading = true;
    state.comparisonCollapsed.code = true;
  }
}

function recommendedStage(prop) {
  if (!methodDraftOrSavedScored(prop.id, methodIdForSlot("A", prop))) return "A";
  if (!methodDraftOrSavedScored(prop.id, methodIdForSlot("B", prop))) return "B";
  return "compare";
}

function stageMethodId(prop = state.current) {
  const stage = stageForProp(prop);
  return stage === "A" || stage === "B" ? methodIdForSlot(stage, prop) : "";
}

function stageLabel(stage = stageForProp()) {
  if (stage === "compare") return "Comparison";
  return `Formalization ${stage}`;
}

function setStage(prop, stage) {
  setStageForProp(prop, stage);
  renderCurrent();
}

function methodPanelForSlot(slot) {
  return slot === "A" ? $("methodACode")?.closest(".method-panel") : $("methodBCode")?.closest(".method-panel");
}

function methodToggleForSlot(slot) {
  return slot === "A" ? $("toggleMethodA") : $("toggleMethodB");
}

function methodFiles(methodId, method) {
  if (!method) return [];
  return [...(method.files || []), ...Object.values(state.externalFiles[methodId] || {})];
}

function methodFile(methodId, method, filePath) {
  return methodFiles(methodId, method).find((file) => file.path === filePath);
}

function ensureOpenFiles(methodId, method) {
  const files = methodFiles(methodId, method);
  const mainPath = files[0]?.path;
  const available = new Set(files.map((file) => file.path));
  const open = (state.openFiles[methodId] || [mainPath]).filter((path) => path && available.has(path));
  if (mainPath && !open.includes(mainPath)) open.unshift(mainPath);
  state.openFiles[methodId] = open.length ? open : (mainPath ? [mainPath] : []);
  return state.openFiles[methodId];
}

function openMethodFile(methodId, filePath) {
  const method = state.current?.methods?.[methodId];
  if (!methodFiles(methodId, method).some((file) => file.path === filePath)) return false;
  const open = ensureOpenFiles(methodId, method);
  if (!open.includes(filePath)) open.push(filePath);
  state.activeFiles[methodId] = filePath;
  return true;
}

function registerExternalFile(methodId, file) {
  if (!file?.path || !file?.lines?.length) return false;
  state.externalFiles[methodId] = state.externalFiles[methodId] || {};
  state.externalFiles[methodId][file.path] = file;
  return true;
}

function closeMethodFile(methodId, filePath) {
  const method = state.current?.methods?.[methodId];
  const mainPath = method?.files?.[0]?.path;
  if (!method || filePath === mainPath) return;
  saveCodeScroll(methodId);
  state.openFiles[methodId] = ensureOpenFiles(methodId, method).filter((path) => path !== filePath);
  if (state.activeFiles[methodId] === filePath) state.activeFiles[methodId] = mainPath;
  renderCode(codeContainer(methodId), state.current, methodId);
}

function fileTabKind(_file, path, mainPath) {
  if (path === mainPath) return "main";
  return "file";
}

function fileTabLabel(method, methodId, path) {
  const files = methodFiles(methodId, method);
  const mainPath = method.files?.[0]?.path;
  if (path === mainPath) return "Main";
  const index = files.findIndex((file) => file.path === path);
  return index >= 1 ? `F${index}` : "F";
}

function fileTabsHtml(method, methodId, activePath) {
  const open = ensureOpenFiles(methodId, method);
  if (!open.length) return "";
  const mainPath = method.files?.[0]?.path;
  const filesByPath = Object.fromEntries(methodFiles(methodId, method).map((file) => [file.path, file]));
  return `
    <div class="file-tabs" role="tablist" aria-label="${escapeHtml(methodDisplayLabel(methodId))} open files">
      ${open.map((path) => {
        const label = fileTabLabel(method, methodId, path);
        const file = filesByPath[path];
        const kind = fileTabKind(file, path, mainPath);
        const close = path !== mainPath ? `<button class="file-tab-close" data-close-file="${escapeHtml(path)}" title="Close file ${escapeHtml(label)}" aria-label="Close file ${escapeHtml(label)}">×</button>` : "";
        return `
          <div class="file-tab-wrap tab-${kind} ${path === activePath ? "active" : ""}">
            <button class="file-tab ${path === activePath ? "active" : ""}"
              data-method="${methodId}" data-file-tab="${escapeHtml(path)}" title="${escapeHtml(methodDisplayLabel(methodId))} file ${escapeHtml(label)}">
              ${escapeHtml(label)}
            </button>
            ${close}
          </div>
        `;
      }).join("")}
    </div>
  `;
}

function codeScrollKey(methodId, filePath) {
  return `${methodId}::${filePath || ""}`;
}

function saveCodeScroll(methodId, container = codeContainer(methodId)) {
  const pane = container?.querySelector(".code-pane");
  const filePath = state.activeFiles[methodId];
  if (!pane || !filePath) return;
  state.codeScroll[codeScrollKey(methodId, filePath)] = {
    top: pane.scrollTop,
    left: pane.scrollLeft,
  };
}

function restoreCodeScroll(methodId, filePath) {
  const saved = state.codeScroll[codeScrollKey(methodId, filePath)];
  if (!saved) return;
  requestAnimationFrame(() => {
    const pane = codeContainer(methodId)?.querySelector(".code-pane");
    if (!pane) return;
    pane.scrollTop = saved.top || 0;
    pane.scrollLeft = saved.left || 0;
  });
}

function wrapIndentCh(text) {
  let count = 0;
  for (const ch of String(text || "")) {
    if (ch === " ") count += 1;
    else if (ch === "\t") count += 2;
    else break;
  }
  return Math.min(32, count + 2);
}

function visibleLeanLines(file) {
  return (file.lines || []).filter((line) => {
    const text = String(line.text || "").trim();
    if (!text) return false;
    if (text.startsWith("import ")) return false;
    if (text.startsWith("set_option ")) return false;
    if (text.startsWith("namespace ")) return false;
    if (text.startsWith("end ")) return false;
    return true;
  });
}

function renderCode(container, prop, methodId, options = {}) {
  const restoreScroll = options.restoreScroll !== false;
  const method = prop.methods[methodId];
  if (!method?.available) {
    container.innerHTML = `<div class="code-empty">${escapeHtml(methodDisplayLabel(methodId, prop))} is not available for this proposition yet.</div>`;
    return;
  }

  const files = methodFiles(methodId, method);
  const openFiles = ensureOpenFiles(methodId, method);
  const activePath = openFiles.includes(state.activeFiles[methodId])
    ? state.activeFiles[methodId]
    : openFiles[0] || files[0]?.path;
  state.activeFiles[methodId] = activePath;
  const file = files.find((f) => f.path === activePath) || files[0];
  if (!file) {
    container.innerHTML = `<div class="code-empty">No Lean source file was extracted.</div>`;
    return;
  }

  const tabs = fileTabsHtml(method, methodId, file.path);
  const lines = visibleLeanLines(file);

  container.innerHTML = `
    ${tabs}
    <div class="code-pane wrap-code">
      ${lines.map((line) => `
        <button class="code-line ${state.activeLine && state.activeLine.methodId === methodId && state.activeLine.filePath === file.path && Number(state.activeLine.line) === Number(line.line) ? "active" : ""}" type="button" tabindex="-1" data-method="${methodId}" data-file="${escapeHtml(file.path)}" data-line="${line.line}">
          <span class="ln">${line.line}</span>${mappingBadgeHtml(method, file.path, line.line)}<span class="src" style="--wrap-indent:${wrapIndentCh(line.text)}ch" data-source-text="${escapeHtml(line.text || " ")}">${sourceLineHtml(method, file, line, null, null, state.activeLine && state.activeLine.methodId === methodId && state.activeLine.filePath === file.path && Number(state.activeLine.line) === Number(line.line) ? state.activeLine.column : null)}</span>
        </button>
      `).join("")}
    </div>
  `;
  container.querySelectorAll(".file-tab").forEach((btn) => {
    btn.addEventListener("click", () => {
      saveCodeScroll(methodId, container);
      state.activeFiles[methodId] = btn.dataset.fileTab;
      renderCode(container, prop, methodId);
    });
  });
  container.querySelectorAll("[data-close-file]").forEach((btn) => {
    btn.addEventListener("click", (event) => {
      event.stopPropagation();
      closeMethodFile(methodId, btn.dataset.closeFile);
    });
  });
  container.querySelector(".code-pane")?.addEventListener("scroll", () => {
    saveCodeScroll(methodId, container);
  }, { passive: true });
  container.querySelectorAll(".code-line").forEach((btn) => {
    btn.addEventListener("click", async (event) => {
      if ((event.ctrlKey || event.metaKey) && await openDependencyAtPointer(prop, methodId, btn, event)) {
        event.preventDefault();
        return;
      }
      inspectLeanLine(prop.id, methodId, btn.dataset.file, Number(btn.dataset.line), btn, codeColumnFromEvent(btn, event));
    });
    btn.addEventListener("pointermove", (event) => {
      updateCtrlClickAffordance(prop, methodId, btn, event);
      queueLeanSourceHover(prop.id, methodId, btn.dataset.file, btn, event);
    });
    btn.addEventListener("pointerout", (event) => {
      if (event.relatedTarget && btn.contains(event.relatedTarget)) return;
      clearCtrlClickAffordance();
      scheduleLeanInfoPopupHide(event);
    });
  });
  container.querySelectorAll(".code-map-badge").forEach((badge) => {
    badge.addEventListener("click", (event) => {
      event.preventDefault();
      event.stopPropagation();
    });
    badge.addEventListener("pointerenter", (event) => {
      event.stopPropagation();
      hideLeanInfoPopup();
      showLineMappingPopup(prop, methodId, badge, event);
    });
    badge.addEventListener("pointermove", (event) => {
      positionLineMappingPopup(badge, event);
    });
    badge.addEventListener("pointerleave", hideLineMappingPopup);
  });
  if (restoreScroll) restoreCodeScroll(methodId, file.path);
}

function lineMappingPopup() {
  let el = $("lineMappingPopup");
  if (!el) {
    el = document.createElement("div");
    el.id = "lineMappingPopup";
    el.className = "line-mapping-popup hidden";
    document.body.appendChild(el);
  }
  return el;
}

function positionLineMappingPopup(anchor, event = null) {
  const popup = lineMappingPopup();
  const rect = anchor.getBoundingClientRect();
  const width = Math.min(520, window.innerWidth - 24);
  const leftAnchor = typeof event?.clientX === "number" ? event.clientX + 12 : rect.left;
  const topAnchor = typeof event?.clientY === "number" ? event.clientY + 18 : rect.bottom + 8;
  const height = popup.offsetHeight || 220;
  popup.style.maxWidth = `${width}px`;
  popup.style.left = `${Math.min(window.innerWidth - width - 12, Math.max(12, leftAnchor))}px`;
  popup.style.top = `${Math.min(window.innerHeight - height - 12, Math.max(12, topAnchor))}px`;
}

function mappingRangeLabel(method, methodId, range) {
  const label = fileTabLabel(method, methodId, range.file);
  return `${label}:${Number(range.start_line)}${Number(range.end_line) !== Number(range.start_line) ? `-${Number(range.end_line)}` : ""}`;
}

function renderLineMappingPopup(prop, method, methodId, mappings) {
  return mappings.map((mapping) => {
    const ranges = (mapping.code_ranges || []).map((range) =>
      `<code>${escapeHtml(mappingRangeLabel(method, methodId, range))}</code>`
    ).join(" ");
    return `
      <section class="line-mapping-section">
        <div class="line-mapping-head">
          <b>${escapeHtml(sentenceLabel(mapping.sentence_ids))}</b>
        </div>
        <div class="line-mapping-ranges">${ranges}</div>
        ${mapping.rationale ? `<p>${escapeHtml(mapping.rationale)}</p>` : ""}
      </section>
    `;
  }).join("");
}

function setLineMappingHighlight(methodId, mappings, enabled) {
  const mappingIds = mappings.map((mapping) => mapping.id);
  const sentenceIds = new Set(
    mappings.flatMap((mapping) => mapping.sentence_ids || []).map((id) => String(id).toLowerCase())
  );
  activeMappingMethod = enabled ? methodId : "";
  activeMappingIds = enabled ? mappingIds : [];
  document.querySelectorAll(`.code-line[data-method="${CSS.escape(methodId)}"]`).forEach((line) => {
    const file = line.dataset.file;
    const lineNumber = Number(line.dataset.line);
    const mapped = mappings.some((mapping) =>
      (mapping.code_ranges || []).some((range) =>
        range.file === file &&
        Number(range.start_line) <= lineNumber &&
        lineNumber <= Number(range.end_line)
      )
    );
    line.classList.toggle("code-line-mapped-range", enabled && mapped);
  });
  document.querySelectorAll(".nl-sentence").forEach((sentence) => {
    sentence.classList.toggle(
      "nl-sentence-mapped-range",
      enabled && sentenceIds.has(String(sentence.dataset.sentenceId || "").toLowerCase())
    );
  });
}

function showLineMappingPopup(prop, methodId, badge, event) {
  const method = prop.methods[methodId];
  const ids = decodeAttrJson(badge.dataset.mappingIds) || [];
  const mappings = (method.line_text_mappings || []).filter((mapping) => ids.includes(mapping.id));
  if (!mappings.length) return;
  const popup = lineMappingPopup();
  popup.innerHTML = renderLineMappingPopup(prop, method, methodId, mappings);
  popup.classList.remove("hidden");
  setLineMappingHighlight(methodId, mappings, true);
  positionLineMappingPopup(badge, event);
}

function hideLineMappingPopup() {
  lineMappingPopup().classList.add("hidden");
  if (activeMappingMethod) {
    const method = state.current?.methods?.[activeMappingMethod];
    const mappings = (method?.line_text_mappings || []).filter((mapping) => activeMappingIds.includes(mapping.id));
    setLineMappingHighlight(activeMappingMethod, mappings, false);
  }
  activeMappingMethod = "";
  activeMappingIds = [];
}

function sourceLineDeps(method, filePath, lineNumber) {
  const line = (method.files || [])
    .find((file) => file.path === filePath)
    ?.lines?.find((item) => Number(item.line) === Number(lineNumber));
  const text = line?.text || "";
  const extracted = (method.dependencies || [])
    .filter((dep) => dep.kind !== "automation" && dep.file === filePath && Number(dep.line) === Number(lineNumber) && dep.label)
    .map((dep) => ({ kind: dep.kind, label: dep.label }));
  return [...extracted, ...inBookReferenceDeps(method, text)];
}

function inBookReferenceDeps(method, text) {
  const deps = [];
  const files = method.files || [];
  const hasStepFile = (step) => files.some((file) => shortFileName(file.path) === `step${step}.lean`);
  for (const match of text.matchAll(/\bhelper_\d+_\d+_step(\d+)\b/g)) {
    if (hasStepFile(match[1])) deps.push({ kind: "helper", label: match[0] });
  }
  for (const match of text.matchAll(/\bBook\d+\.Prop\d+\.step(\d+)\b/g)) {
    if (hasStepFile(match[1])) deps.push({ kind: "helper", label: match[0] });
  }
  return deps;
}

function dependencyRangesForText(text, deps) {
  const ranges = [];
  for (const dep of deps) {
    let start = text.indexOf(dep.label);
    while (start >= 0) {
      ranges.push({ ...dep, start, end: start + dep.label.length });
      start = text.indexOf(dep.label, start + dep.label.length);
    }
  }
  return ranges;
}

const LEAN_KEYWORDS = new Set([
  "abbrev", "axiom", "class", "def", "deriving", "example", "import", "inductive", "instance",
  "namespace", "open", "opaque", "section", "structure", "theorem", "variable", "where",
  "as", "at", "by", "calc", "case", "do", "else", "end", "for", "from", "fun", "have", "if",
  "in", "let", "match", "mutual", "of", "then", "show", "suffices", "syntax", "term",
  "unless", "using", "with", "Prop", "Sort", "Type",
]);

function leanSyntaxRanges(text) {
  const ranges = [];
  let i = 0;
  while (i < text.length) {
    const two = text.slice(i, i + 2);
    if (two === "--") {
      ranges.push({ start: i, end: text.length, cls: "lean-syn-comment" });
      break;
    }
    if (two === "/-") {
      const end = text.indexOf("-/", i + 2);
      ranges.push({ start: i, end: end >= 0 ? end + 2 : text.length, cls: "lean-syn-comment" });
      i = end >= 0 ? end + 2 : text.length;
      continue;
    }
    if (text[i] === '"') {
      let end = i + 1;
      while (end < text.length) {
        if (text[end] === "\\" && end + 1 < text.length) {
          end += 2;
          continue;
        }
        if (text[end] === '"') {
          end += 1;
          break;
        }
        end += 1;
      }
      ranges.push({ start: i, end, cls: "lean-syn-string" });
      i = end;
      continue;
    }
    if (/[A-Za-z_]/.test(text[i])) {
      const start = i;
      i += 1;
      while (i < text.length && /[A-Za-z0-9_'.]/.test(text[i])) i += 1;
      const word = text.slice(start, i);
      if (LEAN_KEYWORDS.has(word)) ranges.push({ start, end: i, cls: "lean-syn-keyword" });
      continue;
    }
    if (/\d/.test(text[i])) {
      const start = i;
      i += 1;
      while (i < text.length && /[0-9_]/.test(text[i])) i += 1;
      ranges.push({ start, end: i, cls: "lean-syn-number" });
      continue;
    }
    i += 1;
  }
  return ranges;
}

function escapeCodeChunk(text) {
  return escapeHtml(text)
    .replace(/(:=|=&gt;|→|,|;)/g, "$1<wbr>")
    .replace(/(\))(\s+)/g, "$1<wbr>$2")
    .replace(/(\s)(by|have|show|from|exact|apply|rw|simp|constructor|cases)(\s)/g, "$1<wbr>$2$3");
}

function sourceLineHtml(method, file, line, highlight = null, clickHint = null, caretColumn = null) {
  const text = line.text || " ";
  const deps = dependencyRangesForText(text, sourceLineDeps(method, file.path, line.line));
  const syntax = leanSyntaxRanges(text);
  const caret = caretColumn === null || caretColumn === undefined
    ? null
    : Math.max(0, Math.min(text.length, Number(caretColumn) || 0));
  const boundaries = new Set([0, text.length]);
  if (caret !== null) boundaries.add(caret);
  if (highlight) {
    boundaries.add(highlight.start);
    boundaries.add(highlight.end);
  }
  if (clickHint) {
    boundaries.add(clickHint.start);
    boundaries.add(clickHint.end);
  }
  deps.forEach((dep) => {
    boundaries.add(dep.start);
    boundaries.add(dep.end);
  });
  syntax.forEach((range) => {
    boundaries.add(range.start);
    boundaries.add(range.end);
  });
  const points = [...boundaries].filter((n) => n >= 0 && n <= text.length).sort((a, b) => a - b);
  const html = points.slice(0, -1).map((start, idx) => {
    const end = points[idx + 1];
    const chunk = text.slice(start, end);
    const caretHtml = caret === start ? `<span class="lean-caret" aria-hidden="true"></span>` : "";
    if (!chunk) return caretHtml;
    const classes = [];
    const dep = deps.find((item) => item.start <= start && end <= item.end);
    const syntaxRange = syntax.find((item) => item.start <= start && end <= item.end);
    if (syntaxRange) classes.push(syntaxRange.cls);
    if (dep) classes.push("book-dependency-token", `dep-kind-${dep.kind}`);
    if (highlight && highlight.start <= start && end <= highlight.end) classes.push("source-hover-token");
    if (clickHint && clickHint.start <= start && end <= clickHint.end) classes.push("ctrl-click-token");
    const title = dep ? `Book dependency: ${dep.label}` : "";
    const chunkHtml = classes.length
      ? `<span class="${classes.join(" ")}" ${title ? `title="${escapeHtml(title)}"` : ""}>${escapeCodeChunk(chunk)}</span>`
      : escapeCodeChunk(chunk);
    return caretHtml + chunkHtml;
  }).join("");
  return html + (caret === text.length ? `<span class="lean-caret" aria-hidden="true"></span>` : "");
}

function codeLineContext(methodId, btn) {
  const method = state.current?.methods?.[methodId];
  const file = methodFiles(methodId, method).find((f) => f.path === btn?.dataset.file);
  const line = file?.lines?.find((l) => Number(l.line) === Number(btn?.dataset.line));
  return { method, file, line };
}

function renderCodeLineSource(methodId, btn, hoverBounds = null, clickBounds = null) {
  const src = btn?.querySelector(".src");
  const { method, file, line } = codeLineContext(methodId, btn);
  if (!src) return;
  const text = src.dataset.sourceText || src.textContent || " ";
  const caretColumn = state.activeLine &&
    state.activeLine.methodId === methodId &&
    state.activeLine.filePath === btn?.dataset.file &&
    Number(state.activeLine.line) === Number(btn?.dataset.line)
      ? state.activeLine.column
      : null;
  src.innerHTML = method && file && line
    ? sourceLineHtml(method, file, line, hoverBounds, clickBounds, caretColumn)
    : escapeHtml(text);
}

function ctrlClickBoundsAtPointer(btn, event) {
  const src = btn?.querySelector(".src");
  const text = src?.dataset.sourceText || src?.textContent || "";
  const column = hoverColumnFromEvent(btn, event);
  if (column === null) return null;
  const bounds = sourceLeanClickableBounds(text, column);
  return bounds ? { ...bounds, column } : null;
}

function ctrlClickColumnFromBounds(bounds) {
  if (!bounds) return null;
  const fallback = Number(bounds.start) || 0;
  return Math.max(0, Math.min(Number(bounds.end) - 1, Number(bounds.column ?? fallback) || 0));
}

function ctrlClickDefinitionColumns(btn, bounds) {
  const primary = ctrlClickColumnFromBounds(bounds);
  return primary === null ? [] : [primary];
}

function identifierFromBounds(btn, bounds) {
  if (!bounds) return "";
  const src = btn?.querySelector(".src");
  const text = src?.dataset.sourceText || src?.textContent || "";
  const start = Math.max(0, Math.min(text.length, Number(bounds.start) || 0));
  const end = Math.max(start, Math.min(text.length, Number(bounds.end) || start));
  const token = text.slice(start, end);
  return /^[A-Za-z_][A-Za-z0-9_']*$/.test(token) && !LEAN_KEYWORDS.has(token) ? token : "";
}

function findNameInText(text, ident, offset = 0) {
  const re = /[A-Za-z_][A-Za-z0-9_']*/g;
  let match;
  while ((match = re.exec(text))) {
    if (match[0] === ident) return offset + match.index;
  }
  return -1;
}

function binderColumnInLine(text, ident) {
  const groupRe = /[\(\{]([^()\{\}:=]+?)\s*:\s*[^()\{\}]+[\)\}]/g;
  let match;
  while ((match = groupRe.exec(text))) {
    const col = findNameInText(match[1], ident, match.index + match[0].indexOf(match[1]));
    if (col >= 0) return col;
  }

  const declarationPatterns = [
    /\b(?:have|let|suffices)\s+([A-Za-z_][A-Za-z0-9_']*)\b/g,
    /\bas\s+([A-Za-z_][A-Za-z0-9_']*)\b/g,
  ];
  for (const re of declarationPatterns) {
    while ((match = re.exec(text))) {
      if (match[1] === ident) return match.index + match[0].lastIndexOf(match[1]);
    }
  }

  const intro = /\bintros?\s+(.+)$/.exec(text);
  if (intro) {
    const col = findNameInText(intro[1], ident, intro.index + intro[0].indexOf(intro[1]));
    if (col >= 0) return col;
  }
  return -1;
}

function localDefinitionAtBounds(prop, methodId, btn, bounds) {
  const ident = identifierFromBounds(btn, bounds);
  if (!ident || !prop?.methods?.[methodId]) return null;
  const method = prop.methods[methodId];
  const file = methodFile(methodId, method, btn.dataset.file);
  if (!file) return null;
  const currentLine = Number(btn.dataset.line);
  let found = null;
  for (const line of file.lines || []) {
    const lineNumber = Number(line.line);
    if (!lineNumber || lineNumber > currentLine) break;
    const column = binderColumnInLine(line.text || "", ident);
    if (column >= 0) {
      found = { filePath: file.path, line: lineNumber, column, local: true };
    }
  }
  return found;
}

function sameSourceBounds(a, b) {
  return !!a && !!b &&
    Number(a.start) === Number(b.start) &&
    Number(a.end) === Number(b.end) &&
    Number(a.column ?? a.start) === Number(b.column ?? b.start);
}

function activeCtrlClickBoundsForButton(btn) {
  return ctrlClickAffordance?.btn === btn ? ctrlClickAffordance.bounds : null;
}

function ctrlClickLookupKey(prop, methodId, btn, bounds) {
  if (!bounds) return "";
  return `${prop.id}::${methodId}::${btn.dataset.file}::${btn.dataset.line}::${bounds.start}-${bounds.end}:${bounds.column ?? bounds.start}`;
}

function pointerWithinSourceBounds(btn, bounds, event, tolerance = 4) {
  const src = btn?.querySelector(".src");
  if (!src || !bounds || typeof event?.clientX !== "number" || typeof event?.clientY !== "number") return false;
  const text = src.dataset.sourceText || src.textContent || "";
  const start = Math.max(0, Math.min(text.length, Number(bounds.start) || 0));
  const end = Math.max(start, Math.min(text.length, Number(bounds.end) || start));
  const a = domPointForSourceOffset(src, start);
  const b = domPointForSourceOffset(src, end);
  if (!a || !b) return false;
  const range = document.createRange();
  try {
    range.setStart(a.node, a.offset);
    range.setEnd(b.node, b.offset);
  } catch (_) {
    return false;
  }
  for (const rect of range.getClientRects()) {
    if (
      event.clientX >= rect.left - tolerance &&
      event.clientX <= rect.right + tolerance &&
      event.clientY >= rect.top - tolerance &&
      event.clientY <= rect.bottom + tolerance
    ) {
      return true;
    }
  }
  return false;
}

function applyCtrlClickAffordance(methodId, btn, bounds) {
  clearTimeout(ctrlClickTimer);
  ctrlClickKey = "";
  if (
    ctrlClickAffordance &&
    ctrlClickAffordance.btn === btn &&
    ctrlClickAffordance.methodId === methodId &&
    sameSourceBounds(ctrlClickAffordance.bounds, bounds)
  ) {
    return;
  }
  if (sourceClickableLine && sourceClickableLine !== btn) clearCtrlClickAffordance();
  renderCodeLineSource(methodId, btn, null, bounds);
  sourceClickableLine = btn;
  ctrlClickAffordance = {
    methodId,
    btn,
    file: btn.dataset.file,
    line: Number(btn.dataset.line),
    bounds: { start: bounds.start, end: bounds.end, column: bounds.column },
  };
}

async function hasLeanDefinitionAtBounds(prop, methodId, btn, bounds) {
  if (!methodFile(methodId, prop.methods[methodId], btn.dataset.file)) return false;
  const key = ctrlClickLookupKey(prop, methodId, btn, bounds);
  if (!key) return false;
  if (state.definitionCache[key] !== undefined) return state.definitionCache[key];
  if (localDefinitionAtBounds(prop, methodId, btn, bounds)) {
    state.definitionCache[key] = true;
    return true;
  }
  try {
    for (const column of ctrlClickDefinitionColumns(btn, bounds)) {
      const data = await leanApi("/api/lean/definition", {
        proposition_id: prop.id,
        method_id: methodId,
        file_path: btn.dataset.file,
        line: Number(btn.dataset.line),
        column,
      });
      if ((data.locations || []).some((item) => item.inManifest || item.source)) {
        state.definitionCache[key] = true;
        return true;
      }
    }
  } catch (err) {
    if (isStaleLeanError(err)) return false;
    console.warn("Lean definition affordance lookup failed", err);
  }
  state.definitionCache[key] = false;
  return false;
}

async function updateCtrlClickAffordance(prop, methodId, btn, event) {
  lastCodePointer = {
    prop,
    methodId,
    btn,
    event: {
      clientX: event.clientX,
      clientY: event.clientY,
      ctrlKey: event.ctrlKey,
      metaKey: event.metaKey,
      target: event.target,
    },
  };
  if (!(event.ctrlKey || event.metaKey)) {
    clearCtrlClickAffordance();
    return;
  }
  if (
    ctrlClickAffordance &&
    ctrlClickAffordance.btn === btn &&
    ctrlClickAffordance.methodId === methodId &&
    ctrlClickAffordance.file === btn.dataset.file &&
    Number(ctrlClickAffordance.line) === Number(btn.dataset.line) &&
    pointerWithinSourceBounds(btn, ctrlClickAffordance.bounds, event)
  ) {
    return;
  }
  const bounds = ctrlClickBoundsAtPointer(btn, event);
  if (!bounds) {
    clearCtrlClickAffordance();
    return;
  }

  const localDep = dependencyAtBounds(prop, methodId, btn, bounds);
  if (localDep) {
    applyCtrlClickAffordance(methodId, btn, bounds);
    return;
  }

  const key = ctrlClickLookupKey(prop, methodId, btn, bounds);
  if (!key) {
    clearCtrlClickAffordance();
    return;
  }
  if (state.definitionCache[key] === true) {
    applyCtrlClickAffordance(methodId, btn, bounds);
    return;
  }
  if (state.definitionCache[key] === false) {
    clearCtrlClickAffordance();
    return;
  }

  clearTimeout(ctrlClickTimer);
  ctrlClickKey = key;
  ctrlClickTimer = setTimeout(async () => {
    if (ctrlClickKey !== key || !btn.isConnected) return;
    const ok = await hasLeanDefinitionAtBounds(prop, methodId, btn, bounds);
    if (ctrlClickKey !== key || !btn.isConnected) return;
    if (ok) applyCtrlClickAffordance(methodId, btn, bounds);
  }, 120);
}

function refreshCtrlClickAffordance(active) {
  if (!lastCodePointer?.btn?.isConnected) {
    clearCtrlClickAffordance();
    lastCodePointer = null;
    return;
  }
  const event = {
    ...lastCodePointer.event,
    ctrlKey: active,
    metaKey: active,
  };
  updateCtrlClickAffordance(lastCodePointer.prop, lastCodePointer.methodId, lastCodePointer.btn, event);
}

function clearCtrlClickAffordance() {
  clearTimeout(ctrlClickTimer);
  ctrlClickKey = "";
  if (!sourceClickableLine) {
    ctrlClickAffordance = null;
    return;
  }
  const methodId = sourceClickableLine.dataset.method;
  renderCodeLineSource(methodId, sourceClickableLine);
  sourceClickableLine = null;
  ctrlClickAffordance = null;
}

function dependencyAtBounds(prop, methodId, btn, bounds) {
  const method = prop.methods[methodId];
  const src = btn.querySelector(".src");
  const text = src?.dataset.sourceText || src?.textContent || "";
  const column = ctrlClickColumnFromBounds(bounds);
  if (column === null) return null;
  const line = Number(btn.dataset.line);
  const file = btn.dataset.file;
  const extracted = (method.dependencies || []).find((dep) => {
    if (dep.file !== file || Number(dep.line) !== line || !dep.label) return false;
    let start = text.indexOf(dep.label);
    while (start >= 0) {
      const end = start + dep.label.length;
      if (start <= column && column <= end) return true;
      start = text.indexOf(dep.label, end);
    }
    return false;
  });
  if (extracted && !(extracted.file === file && Number(extracted.line) === line)) return extracted;

  const helper = dependencyFileAtColumn(method, text, column, bounds);
  return helper ? { file: helper.file, line: helper.line, label: helper.label } : null;
}

function dependencyAtPointer(prop, methodId, btn, event) {
  const bounds = ctrlClickBoundsAtPointer(btn, event);
  return bounds ? dependencyAtBounds(prop, methodId, btn, bounds) : null;
}

function dependencyFileAtColumn(method, text, column, bounds = null) {
  const files = method.files || [];
  const candidates = [];
  for (const match of text.matchAll(/\bhelper_\d+_\d+_step(\d+)\b/g)) {
    const label = match[0];
    candidates.push({ label, start: match.index, end: match.index + label.length, path: `step${match[1]}.lean` });
  }
  for (const match of text.matchAll(/\bBook\d+\.Prop\d+\.step(\d+)\b/g)) {
    const label = match[0];
    candidates.push({ label, start: match.index, end: match.index + label.length, path: `step${match[1]}.lean` });
  }
  for (const item of candidates) {
    const overlapsBounds = bounds && item.start < bounds.end && bounds.start < item.end;
    if (!overlapsBounds && (item.start > column || column >= item.end)) continue;
    const file = files.find((f) => shortFileName(f.path) === item.path);
    if (!file) continue;
    const theoremLine = (file.lines || []).find((line) => line.text.includes(item.label))?.line || 1;
    return { file: file.path, line: theoremLine, label: item.label };
  }
  return null;
}

async function openDependencyAtPointer(prop, methodId, btn, event) {
  const dep = dependencyAtPointer(prop, methodId, btn, event);
  if (dep) {
    openMethodFile(methodId, dep.file);
    renderCode(codeContainer(methodId), prop, methodId, { restoreScroll: false });
    jumpToCodeLine(methodId, dep.file, Number(dep.line));
    return true;
  }
  try {
    return await openLeanDefinitionAtPointer(prop, methodId, btn, event);
  } catch (err) {
    if (isStaleLeanError(err)) return false;
    console.warn("Lean definition lookup failed", err);
    return false;
  }
}

async function openLeanDefinitionAtPointer(prop, methodId, btn, event) {
  if (!methodFile(methodId, prop.methods[methodId], btn.dataset.file)) return false;
  const activeBounds =
    ctrlClickAffordance &&
    ctrlClickAffordance.btn === btn &&
    ctrlClickAffordance.methodId === methodId &&
    pointerWithinSourceBounds(btn, ctrlClickAffordance.bounds, event)
      ? ctrlClickAffordance.bounds
      : null;
  const bounds = activeBounds || ctrlClickBoundsAtPointer(btn, event);
  const local = localDefinitionAtBounds(prop, methodId, btn, bounds);
  if (local) {
    jumpToCodeLine(methodId, local.filePath, local.line, local.column);
    return true;
  }
  let loc = null;
  for (const column of ctrlClickDefinitionColumns(btn, bounds)) {
    const data = await leanApi("/api/lean/definition", {
      proposition_id: prop.id,
      method_id: methodId,
      file_path: btn.dataset.file,
      line: Number(btn.dataset.line),
      column,
    });
    loc = (data.locations || []).find((item) => item.inManifest || item.source);
    if (loc) break;
  }
  if (!loc) return false;
  if (loc.source) registerExternalFile(methodId, loc.source);
  openMethodFile(methodId, loc.filePath);
  renderCode(codeContainer(methodId), prop, methodId, { restoreScroll: false });
  jumpToCodeLine(methodId, loc.filePath, Number(loc.line || 1), Number(loc.column || 0));
  return true;
}

function defaultLeanColumn(btn) {
  const src = btn?.querySelector(".src");
  const text = src?.dataset.sourceText || src?.textContent || "";
  const firstToken = text.search(/\S/);
  return firstToken >= 0 ? firstToken : 0;
}

function codeLineText(btn) {
  const src = btn?.querySelector(".src");
  return src?.dataset.sourceText || src?.textContent || "";
}

function clampLeanColumn(btn, column) {
  const text = codeLineText(btn);
  return Math.max(0, Math.min(text.length, Number(column) || 0));
}

function domPointForSourceOffset(root, offset) {
  const target = Math.max(0, Number(offset) || 0);
  const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
  let seen = 0;
  let node = walker.nextNode();
  let last = null;
  while (node) {
    last = node;
    const next = seen + node.textContent.length;
    if (target <= next) return { node, offset: target - seen };
    seen = next;
    node = walker.nextNode();
  }
  return last ? { node: last, offset: last.textContent.length } : null;
}

function pointInRangeRect(src, start, end, event) {
  const a = domPointForSourceOffset(src, start);
  const b = domPointForSourceOffset(src, end);
  if (!a || !b) return false;
  const range = document.createRange();
  try {
    range.setStart(a.node, a.offset);
    range.setEnd(b.node, b.offset);
  } catch (_) {
    return false;
  }
  for (const rect of range.getClientRects()) {
    if (
      event.clientX >= rect.left - 1 &&
      event.clientX <= rect.right + 1 &&
      event.clientY >= rect.top - 1 &&
      event.clientY <= rect.bottom + 1
    ) {
      return true;
    }
  }
  return false;
}

function sourceColumnFromPoint(src, event, requireGlyph = false) {
  const text = src?.dataset.sourceText || "";
  if (!src || !text || typeof event?.clientX !== "number" || typeof event?.clientY !== "number") return null;
  const atPoint = document.elementFromPoint(event.clientX, event.clientY);
  if (!atPoint || !(atPoint === src || src.contains(atPoint))) return null;
  const rect = src.getBoundingClientRect();
  if (event.clientX < rect.left || event.clientX > rect.right || event.clientY < rect.top || event.clientY > rect.bottom) return null;

  let node = null;
  let offset = 0;
  if (document.caretPositionFromPoint) {
    const pos = document.caretPositionFromPoint(event.clientX, event.clientY);
    node = pos?.offsetNode || null;
    offset = pos?.offset || 0;
  } else if (document.caretRangeFromPoint) {
    const range = document.caretRangeFromPoint(event.clientX, event.clientY);
    node = range?.startContainer || null;
    offset = range?.startOffset || 0;
  }
  if (!node || !src.contains(node)) return null;

  const range = document.createRange();
  range.selectNodeContents(src);
  try {
    range.setEnd(node, offset);
  } catch (_) {
    return null;
  }
  const column = Math.max(0, Math.min(text.length, range.toString().length));
  if (!requireGlyph) return column;
  const candidates = [column, column - 1]
    .filter((idx, pos, arr) => idx >= 0 && idx < text.length && arr.indexOf(idx) === pos && !/\s/.test(text[idx] || ""));
  for (const idx of candidates) {
    if (pointInRangeRect(src, idx, idx + 1, event)) return idx;
  }
  return null;
}

function codeColumnFromEvent(btn, event) {
  const src = btn?.querySelector(".src");
  const text = src?.dataset.sourceText || src?.textContent || "";
  if (!src || typeof event?.clientX !== "number" || event.clientX <= 0) return defaultLeanColumn(btn);
  const precise = sourceColumnFromPoint(src, event);
  if (precise !== null) return precise;
  const styles = getComputedStyle(src);
  const canvas = codeColumnFromEvent.canvas || (codeColumnFromEvent.canvas = document.createElement("canvas"));
  const ctx = canvas.getContext("2d");
  ctx.font = styles.font;
  const charWidth = Math.max(1, ctx.measureText("M").width);
  const rect = src.getBoundingClientRect();
  const paddingLeft = parseFloat(styles.paddingLeft || "0");
  const x = event.clientX - rect.left - paddingLeft + src.scrollLeft;
  return Math.max(0, Math.min(text.length, Math.round(x / charWidth)));
}

function hoverColumnFromEvent(btn, event) {
  const src = btn?.querySelector(".src");
  const text = src?.dataset.sourceText || src?.textContent || "";
  if (!src || !text || typeof event?.clientX !== "number") return null;
  const precise = sourceColumnFromPoint(src, event, true);
  if (precise !== null) {
    const column = Math.max(0, Math.min(text.length - 1, precise));
    if (/\s/.test(text[column] || "")) return null;
    return column;
  }
  const styles = getComputedStyle(src);
  const canvas = codeColumnFromEvent.canvas || (codeColumnFromEvent.canvas = document.createElement("canvas"));
  const ctx = canvas.getContext("2d");
  ctx.font = styles.font;
  const charWidth = Math.max(1, ctx.measureText("M").width);
  const textWidth = ctx.measureText(text).width;
  const rect = src.getBoundingClientRect();
  const paddingLeft = parseFloat(styles.paddingLeft || "0");
  const x = event.clientX - rect.left - paddingLeft + src.scrollLeft;
  if (x < 0 || x > textWidth + charWidth * 0.35) return null;
  const column = Math.max(0, Math.min(text.length - 1, Math.round(x / charWidth)));
  if (/\s/.test(text[column] || "")) return null;
  return column;
}

function findRenderedCodeLine(methodId, filePath, line) {
  const lines = Array.from(document.querySelectorAll(`.code-line[data-method="${methodId}"]`));
  return lines.find((el) => el.dataset.file === filePath && Number(el.dataset.line) === Number(line));
}

function firstVisibleCodeLine(methodId) {
  const viewportHeight = window.innerHeight || document.documentElement.clientHeight || 0;
  return Array.from(document.querySelectorAll(`.code-line[data-method="${methodId}"]`)).find((el) => {
    if (!isUsableTutorialTarget(el)) return false;
    const rect = el.getBoundingClientRect();
    if (rect.bottom <= 0 || rect.top >= viewportHeight) return false;
    const pane = el.closest(".code-pane");
    if (!pane) return true;
    const paneRect = pane.getBoundingClientRect();
    return rect.bottom > paneRect.top && rect.top < paneRect.bottom;
  }) || null;
}

function jumpToCodeLine(methodId, filePath, line, column = 0) {
  let target = findRenderedCodeLine(methodId, filePath, line);
  if (!target && methodFiles(methodId, state.current?.methods[methodId]).some((file) => file.path === filePath)) {
    openMethodFile(methodId, filePath);
    renderCode(codeContainer(methodId), state.current, methodId, { restoreScroll: false });
    target = findRenderedCodeLine(methodId, filePath, line);
  }
  if (!target) return;
  target.scrollIntoView({ block: "center", behavior: "smooth" });
  inspectLeanLine(state.current.id, methodId, filePath, Number(line), target, Number(column) || 0);
}

function metricStandardsHtml(metric, selected, methodId, enabled) {
  return metric.score_options.map((o) => `
    <button class="metric-standard-row metric-standard-button ${selected === o.score ? "selected" : ""}"
      type="button"
      data-standard-metric="${escapeHtml(metric.id)}"
      data-standard-score="${o.score}"
      data-method="${escapeHtml(methodId)}"
      data-metric="${escapeHtml(metric.id)}"
      data-score="${o.score}"
      ${!enabled ? "disabled" : ""}
      title="Score ${o.score}: ${escapeHtml(o.label)}">
      <span class="metric-standard-score">${o.score}</span>
      <span class="metric-standard-copy">
        <b>${escapeHtml(o.label)}</b>
        <span>${escapeHtml(o.standard)}</span>
      </span>
    </button>
  `).join("");
}

function setMetricStandardHighlight(metricId, score = null) {
  const card = document.querySelector(`[data-metric-card="${CSS.escape(metricId)}"]`);
  if (!card) return;
  card.querySelectorAll(".metric-standard-row").forEach((row) => {
    row.classList.toggle("active", score !== null && row.dataset.standardScore === String(score));
  });
}

function renderMetricCards(prop) {
  const wrap = $("metricCards");
  const stage = stageForProp(prop);
  const enabled = ready({
    methodAvailability: {
      leaneuclid: prop.methods.leaneuclid.available,
      new_method: prop.methods.new_method.available,
    },
  }) && isAssigned(prop.id);
  if (stage === "compare") {
    renderPreferenceCards(prop, enabled);
    return;
  }
  const methodId = stageMethodId(prop);
  const method = prop.methods[methodId];
  wrap.innerHTML = state.config.rubric.metrics.map((metric) => {
    const selected = getScore(prop.id, methodId, metric.id);
    const scoreEnabled = enabled && method.available;
    const standards = metricStandardsHtml(metric, selected, methodId, scoreEnabled);
    return `
      <article class="metric-card metric-card-single" data-metric-card="${metric.id}">
        <div class="metric-card-head">
          <div class="metric-summary">
            <h3>${escapeHtml(metric.title)}</h3>
            <p class="metric-prompt">${escapeHtml(metric.prompt)}</p>
          </div>
        </div>
        <div class="metric-detail" id="detail-${metric.id}">${standards}</div>
      </article>
    `;
  }).join("");

  wrap.querySelectorAll(".metric-standard-button").forEach((btn) => {
    btn.addEventListener("mouseenter", () => setMetricStandardHighlight(btn.dataset.metric, btn.dataset.score));
    btn.addEventListener("mouseleave", () => setMetricStandardHighlight(btn.dataset.metric));
    btn.addEventListener("focus", () => setMetricStandardHighlight(btn.dataset.metric, btn.dataset.score));
    btn.addEventListener("blur", () => setMetricStandardHighlight(btn.dataset.metric));
    btn.addEventListener("click", () => {
      const key = responseKey(prop.id, btn.dataset.method, btn.dataset.metric);
      state.draft[key] = {
        ...(state.draft[key] || {}),
        score: Number(btn.dataset.score),
      };
      renderMetricCards(prop);
      renderPropList();
      renderStagePanel(prop);
      scheduleAutosave(prop);
    });
  });
}

function preferenceLabel(value, prop) {
  if (value < 0) return `${Math.abs(value)} toward Formalization A`;
  if (value > 0) return `${value} toward Formalization B`;
  return "Neutral";
}

function renderPreferenceCards(prop, enabled) {
  const wrap = $("metricCards");
  const questions = preferenceQuestions();
  wrap.innerHTML = `
    <div class="preference-cards">
      ${questions.map((question) => {
        const selected = uiPreferenceChoice(prop, getPreference(prop.id, question.id));
        return `
          <article class="preference-card" data-preference-card="${escapeHtml(question.id)}">
            <div>
              <h3>${question.number}. ${escapeHtml(question.title)}</h3>
              <p class="metric-prompt">${escapeHtml(question.prompt)}</p>
            </div>
            <div class="preference-scale" role="radiogroup" aria-label="${escapeHtml(question.title)}">
              <span class="preference-end preference-a">A</span>
              ${[-3, -2, -1, 0, 1, 2, 3].map((value) => `
                <button class="preference-dot pref-${value < 0 ? "a" : value > 0 ? "b" : "neutral"} pref-strength-${Math.abs(value)} ${selected === value ? "selected" : ""}"
                  type="button"
                  data-question="${escapeHtml(question.id)}"
                  data-choice="${value}"
                  ${!enabled ? "disabled" : ""}
                  title="${escapeHtml(preferenceLabel(value, prop))}"
                  aria-label="${escapeHtml(preferenceLabel(value, prop))}"></button>
              `).join("")}
              <span class="preference-end preference-b">B</span>
            </div>
          </article>
        `;
      }).join("")}
    </div>
  `;
  wrap.querySelectorAll(".preference-dot").forEach((btn) => {
    btn.addEventListener("click", () => {
      const key = preferenceKey(prop.id, btn.dataset.question);
      state.draft[key] = { choice: canonicalPreferenceChoice(prop, btn.dataset.choice) };
      renderMetricCards(prop);
      renderPropList();
      renderStagePanel(prop);
      scheduleAutosave(prop);
    });
  });
}

function leanSourceJumpHtml(line, column = 0, label = "Go to source") {
  if (!line) return "";
  return `
    <button class="source-jump" type="button" data-source-line="${Number(line)}" data-source-column="${Number(column) || 0}" title="${escapeHtml(label)}" aria-label="${escapeHtml(label)}">
      ${Number(line)}:${Number(column) || 0}
    </button>
  `;
}

function leanMessageHtml(messages) {
  return (messages || []).map((m) => `
    <div class="message ${m.severity || ""}">
      <div class="message-head">
        <b>${escapeHtml(m.severity || "info")}</b>
        ${leanSourceJumpHtml(m.line, m.column ?? 0)}
        ${m.source ? `<span class="message-meta">${escapeHtml(m.source)}</span>` : ""}
        ${m.code ? `<code class="message-code">${escapeHtml(m.code)}</code>` : ""}
        ${m.range ? `<span class="message-meta">${escapeHtml(rangeLabel(m.range))}</span>` : ""}
      </div>
      ${m.tags?.length ? `<div class="message-tags">${m.tags.map((tag) => `<span>${escapeHtml(tag)}</span>`).join("")}</div>` : ""}
      <div class="lean-message-tree">${leanMessageTreeHtml(m.messageTree, m.messageCode, m.message || "")}</div>
    </div>
  `).join("") || `<p class="subtle">No Lean diagnostics near this line.</p>`;
}

function leanInfoRefAttr(infoRef) {
  return infoRef ? ` data-info-ref="${encodeAttrJson(infoRef)}"` : "";
}

function leanCodeHtml(code, fallback = "", options = {}) {
  const hoverable = options.hoverable !== false;
  const segments = code?.segments;
  if (!segments?.length) return escapeHtml(code?.text ?? fallback ?? "");
  return segments.map((segment) => {
    const text = escapeHtml(segment.text || "");
    if (!hoverable || !segment.infoRef) return text;
    return `<span class="lean-hover-fragment"${leanInfoRefAttr(segment.infoRef)} data-subexpr-pos="${escapeHtml(segment.subexprPos || "")}">${text}</span>`;
  }).join("");
}

function leanMessageTreeHtml(tree, fallbackCode, fallback = "") {
  const parts = tree?.parts;
  if (!parts?.length) return `<span class="lean-code">${leanCodeHtml(fallbackCode, fallback)}</span>`;
  return parts.map(leanMessagePartHtml).join("");
}

function leanMessagePartHtml(part) {
  if (!part) return "";
  if (part.kind === "text") return escapeHtml(part.text || "");
  if (part.kind === "code") return `<span class="lean-code">${leanCodeHtml(part.code, part.code?.text || "")}</span>`;
  if (part.kind === "goal") return `<div class="embedded-goal">${leanGoalsHtml([part.goal], "")}</div>`;
  if (part.kind === "trace") return leanTraceHtml(part);
  return `<span class="lean-code">${escapeHtml(part.text || "")}</span>`;
}

function leanTraceHtml(trace) {
  const hasStrictChildren = trace.children?.length;
  return `
    <details class="trace-node" ${trace.collapsed ? "" : "open"}>
      <summary>
        <span class="trace-class">${escapeHtml(trace.class || "trace")}</span>
        <span class="trace-header">${leanMessageTreeHtml(trace.header)}</span>
      </summary>
      <div class="trace-children">
        ${hasStrictChildren ? trace.children.map(leanMessageTreeHtml).map((html) => `<div class="trace-child">${html}</div>`).join("") : ""}
        ${!hasStrictChildren ? `<p class="subtle">No trace children.</p>` : ""}
      </div>
    </details>
  `;
}

function orderedGoals(goals) {
  return [...(goals || [])];
}

function visibleHyps(goal) {
  return goal?.hyps || [];
}

function hiddenHypCount(goal) {
  return Math.max(0, (goal?.hyps || []).length - visibleHyps(goal).length);
}

function hypValueHtml(hyp) {
  if (!hyp.valueCode) return "";
  return ` := ${leanCodeHtml(hyp.valueCode, hyp.value || "")}`;
}

function leanHypRowsHtml(goal) {
  const hyps = visibleHyps(goal);
  const hidden = hiddenHypCount(goal);
  const rows = hyps.map((hyp) => `
    <div class="hyp-row ${hyp.isInserted ? "inserted" : ""} ${hyp.isRemoved ? "removed" : ""}">
      <span class="hyp-name">${escapeHtml((hyp.names || []).join(" "))}</span>
      <span class="hyp-colon">:</span>
      <code class="lean-code">${leanCodeHtml(hyp.typeCode, hyp.type || "")}${hypValueHtml(hyp)}</code>
    </div>
  `).join("");
  return rows
    || (hidden ? `<p class="subtle">${hidden} hidden local hypoth${hidden === 1 ? "esis" : "eses"}.</p>` : `<p class="subtle">No local hypotheses.</p>`);
}

function leanGoalsHtml(goals, fallbackGoal) {
  if (goals?.length) {
    return orderedGoals(goals).map((goal, idx) => `
      <article class="infoview-goal">
        <div class="goal-head">
          <span>Goal ${idx + 1}</span>
          ${goal.userName ? `<code>${escapeHtml(goal.userName)}</code>` : ""}
          ${goal.isInserted ? `<em>inserted</em>` : ""}
          ${goal.isRemoved ? `<em>removed next</em>` : ""}
        </div>
        <div class="hyp-list">
          ${leanHypRowsHtml(goal)}
        </div>
        <div class="target-row">
          <span>${escapeHtml(goal.goalPrefix || "⊢ ")}</span>
          <code class="lean-code">${leanCodeHtml(goal.targetCode, goal.target || "")}</code>
        </div>
      </article>
    `).join("");
  }
  if (fallbackGoal) {
    return `<article class="infoview-goal"><pre>${escapeHtml(fallbackGoal)}</pre></article>`;
  }
  return `<div class="infoview-empty">No goals.</div>`;
}

function diagnosticTally(messages) {
  return (messages || []).reduce((acc, message) => {
    const severity = String(message.severity || "info").toLowerCase();
    if (severity === "error") acc.errors += 1;
    else if (severity === "warning") acc.warnings += 1;
    else acc.infos += 1;
    acc.total += 1;
    return acc;
  }, { errors: 0, warnings: 0, infos: 0, total: 0 });
}

function diagnosticTallyHtml(messages) {
  const tally = diagnosticTally(messages);
  if (!tally.total) return "";
  const parts = [];
  if (tally.errors) parts.push(`${tally.errors} error${tally.errors === 1 ? "" : "s"}`);
  if (tally.warnings) parts.push(`${tally.warnings} warning${tally.warnings === 1 ? "" : "s"}`);
  if (tally.infos) parts.push(`${tally.infos} info${tally.infos === 1 ? "" : "s"}`);
  return `<span title="${escapeHtml(parts.join(", "))}">${tally.total}</span>`;
}

function rangeLabel(range) {
  if (!range?.start || !range?.end) return "";
  return `${range.start.line}:${range.start.column}-${range.end.line}:${range.end.column}`;
}

function shortLocationPath(pathOrUri) {
  const text = String(pathOrUri || "");
  const parts = text.split("/");
  return parts.slice(-3).join("/") || text;
}

function leanTermGoalHtml(termGoal) {
  if (!termGoal) {
    return `<div class="infoview-empty">No expected type is available at this cursor position.</div>`;
  }
  return `
    <article class="infoview-goal term-goal">
      <div class="goal-head">
        <span>Expected Type</span>
        ${termGoal.range ? `<code>${escapeHtml(rangeLabel(termGoal.range))}</code>` : ""}
      </div>
      <div class="hyp-list">
        ${leanHypRowsHtml(termGoal)}
      </div>
      <div class="target-row">
        <span>${escapeHtml(termGoal.goalPrefix || "⊢ ")}</span>
        <code class="lean-code">${leanCodeHtml(termGoal.targetCode, termGoal.target || "")}</code>
      </div>
    </article>
  `;
}

function leanRpcErrorsHtml(errors) {
  if (!errors?.length) {
    return `<div class="infoview-empty">All requested Lean RPC calls completed.</div>`;
  }
  return errors.map((err) => `
    <div class="message warning">
      <b>${escapeHtml(err.label || err.method || "RPC call")}</b>
      <div>${escapeHtml(err.message || "")}</div>
    </div>
  `).join("");
}

function leanStateKey(meta) {
  state.leanStateKey += 1;
  return `lean-state-${state.leanStateKey}`;
}

function registerLeanState(meta, data) {
  const key = leanStateKey(meta);
  state.leanStates[key] = { ...meta, data };
  return key;
}

function stateForElement(el) {
  const key = el?.closest?.("[data-lean-state-key]")?.dataset.leanStateKey;
  return key ? state.leanStates[key] : null;
}

function bindLeanStateActions(root = $("leanContent")) {
  root.querySelectorAll(".source-jump").forEach((button) => {
    button.addEventListener("click", () => jumpFromLeanState(button));
  });
  root.querySelectorAll(".lean-hover-fragment").forEach((fragment) => {
    fragment.addEventListener("pointermove", (event) => queueLeanPanelHover(fragment, event));
    fragment.addEventListener("pointerout", (event) => {
      scheduleLeanInfoPopupHide(event);
    });
  });
}

function jumpFromLeanState(button) {
  const active = stateForElement(button) || state.activeLeanState;
  if (!active?.methodId || !active?.filePath) return;
  const line = Number(button.dataset.sourceLine);
  const column = Number(button.dataset.sourceColumn) || 0;
  if (!line) return;
  jumpToCodeLine(active.methodId, active.filePath, line, column);
}

function leanInfoPopup() {
  let el = $("leanInfoPopup");
  if (!el) {
    el = document.createElement("div");
    el.id = "leanInfoPopup";
    el.className = "lean-info-popup hidden";
    el.addEventListener("pointerleave", (event) => scheduleLeanInfoPopupHide(event));
    document.body.appendChild(el);
  }
  return el;
}

function positionLeanInfoPopup(anchor, event = null) {
  const popup = leanInfoPopup();
  const rect = anchor.getBoundingClientRect();
  const width = Math.min(420, window.innerWidth - 24);
  const leftAnchor = typeof event?.clientX === "number" ? event.clientX + 14 : rect.left;
  const topAnchor = typeof event?.clientY === "number" ? event.clientY + 24 : rect.bottom + 8;
  const height = popup.offsetHeight || 160;
  popup.style.maxWidth = `${width}px`;
  popup.style.left = `${Math.min(window.innerWidth - width - 12, Math.max(12, leftAnchor))}px`;
  popup.style.top = `${Math.min(window.innerHeight - height - 12, Math.max(12, topAnchor))}px`;
}

function renderLeanHoverPopup(data) {
  if (!data?.text) return `<div class="popup-doc">No hover information.</div>`;
  const range = rangeLabel(data.range);
  return `
    ${range ? `<div class="popup-row"><b>Range</b><code>${escapeHtml(range)}</code></div>` : ""}
    <div class="popup-doc">${escapeHtml(data.text)}</div>
  `;
}

function sourceHoverBounds(text, column) {
  if (!text) return null;
  let idx = Math.max(0, Math.min(text.length - 1, Number(column) || 0));
  if (/\s/.test(text[idx] || "")) {
    if (idx > 0 && !/\s/.test(text[idx - 1])) idx -= 1;
    else return null;
  }
  let start = idx;
  let end = idx + 1;
  while (start > 0 && !/\s/.test(text[start - 1])) start -= 1;
  while (end < text.length && !/\s/.test(text[end])) end += 1;
  return start < end ? { start, end } : null;
}

function sourceLeanTokenBounds(text, column) {
  if (!text) return null;
  const idx = Math.max(0, Math.min(text.length - 1, Number(column) || 0));
  const isTokenChar = (ch) => /[A-Za-z0-9_'.]/.test(ch || "");
  let at = idx;
  if (!isTokenChar(text[at]) && at > 0 && isTokenChar(text[at - 1])) at -= 1;
  if (!isTokenChar(text[at])) return null;
  let start = at;
  let end = at + 1;
  while (start > 0 && isTokenChar(text[start - 1])) start -= 1;
  while (end < text.length && isTokenChar(text[end])) end += 1;
  return start < end ? { start, end } : null;
}

function sourceLeanClickableBounds(text, column) {
  const bounds = sourceLeanTokenBounds(text, column);
  if (!bounds) return sourceHoverBounds(text, column);
  const token = text.slice(bounds.start, bounds.end);
  if (!token.includes(".") || /^Book\d*\./.test(token)) return bounds;
  let segmentStart = bounds.start;
  let segmentEnd = bounds.end;
  for (let idx = bounds.start; idx < bounds.end; idx += 1) {
    if (text[idx] !== ".") continue;
    if (idx < column) segmentStart = idx + 1;
    if (idx >= column) {
      segmentEnd = idx;
      break;
    }
  }
  return segmentStart < segmentEnd ? { start: segmentStart, end: segmentEnd } : bounds;
}

function clearSourceHoverHighlight() {
  if (!sourceHoverLine) return;
  const src = sourceHoverLine.querySelector(".src");
  if (src) {
    renderCodeLineSource(sourceHoverLine.dataset.method, sourceHoverLine, null, activeCtrlClickBoundsForButton(sourceHoverLine));
  }
  sourceHoverLine = null;
}

function rangeHoverBounds(text, line, range) {
  if (!text || !range?.start || !range?.end) return null;
  const currentLine = Number(line);
  const startLine = Number(range.start.line);
  const endLine = Number(range.end.line);
  if (currentLine < startLine || currentLine > endLine) return null;

  let start = currentLine === startLine ? Number(range.start.column) : 0;
  let end = currentLine === endLine ? Number(range.end.column) : text.length;
  start = Math.max(0, Math.min(text.length, start));
  end = Math.max(start, Math.min(text.length, end));

  if (end <= start) return null;
  if (startLine !== endLine && end - start > 80) return null;
  return { start, end };
}

function setSourceHoverHighlight(btn, column, range = null) {
  const src = btn?.querySelector(".src");
  if (!src) return;
  if (sourceHoverLine && sourceHoverLine !== btn) clearSourceHoverHighlight();
  const text = src.dataset.sourceText || src.textContent || "";
  const bounds = rangeHoverBounds(text, btn.dataset.line, range) || sourceHoverBounds(text, column);
  if (!bounds) {
    renderCodeLineSource(btn.dataset.method, btn, null, activeCtrlClickBoundsForButton(btn));
    sourceHoverLine = null;
    return;
  }
  const method = state.current?.methods?.[btn.dataset.method];
  const file = methodFiles(btn.dataset.method, method).find((f) => f.path === btn.dataset.file);
  const line = file?.lines?.find((l) => Number(l.line) === Number(btn.dataset.line));
  const clickBounds = activeCtrlClickBoundsForButton(btn);
  src.innerHTML = method && file && line
    ? sourceLineHtml(method, file, line, bounds, clickBounds, state.activeLine && state.activeLine.methodId === btn.dataset.method && state.activeLine.filePath === btn.dataset.file && Number(state.activeLine.line) === Number(btn.dataset.line) ? state.activeLine.column : null)
    : `${escapeHtml(text.slice(0, bounds.start))}<span class="source-hover-token">${escapeHtml(text.slice(bounds.start, bounds.end))}</span>${escapeHtml(text.slice(bounds.end))}`;
  sourceHoverLine = btn;
}

function renderLeanInfoHoverPopup(data) {
  const parts = [];
  if (data?.type?.text || data?.type?.segments?.length) {
    parts.push(`<div class="popup-row"><b>Type</b><code class="lean-code">${leanCodeHtml(data.type, "", { hoverable: false })}</code></div>`);
  }
  if (data?.exprExplicit?.text || data?.exprExplicit?.segments?.length) {
    parts.push(`<div class="popup-row"><b>Explicit Expression</b><code class="lean-code">${leanCodeHtml(data.exprExplicit, "", { hoverable: false })}</code></div>`);
  }
  if (data?.doc) {
    parts.push(`<div class="popup-doc">${escapeHtml(data.doc)}</div>`);
  }
  return parts.join("") || `<div class="popup-doc">No hover information.</div>`;
}

function queueLeanSourceHover(propId, methodId, filePath, btn, event) {
  if (!event.target.closest?.(".src")) {
    hideLeanInfoPopup();
    return;
  }
  const line = Number(btn.dataset.line);
  const column = hoverColumnFromEvent(btn, event);
  if (column === null) {
    hideLeanInfoPopup();
    return;
  }
  const pointer = { clientX: event.clientX, clientY: event.clientY };
  const key = `${propId}::${methodId}::${filePath}::${line}::${column}`;
  clearTimeout(leanHoverHideTimer);
  leanHoverKey = key;
  if (state.leanHoverCache[key]) {
    showLeanSourceHover(propId, methodId, filePath, line, column, btn, pointer, key);
    return;
  }
  scheduleLeanHover(() => {
    showLeanSourceHover(propId, methodId, filePath, line, column, btn, pointer, key).catch((err) => {
      if (isStaleLeanError(err)) return;
      if (leanHoverKey !== key) return;
      const popup = leanInfoPopup();
      popup.classList.remove("hidden");
      positionLeanInfoPopup(btn, pointer);
      popup.innerHTML = `<div class="popup-doc">${escapeHtml(err.message)}</div>`;
    });
  });
}

async function showLeanSourceHover(propId, methodId, filePath, line, column, btn, pointer, key) {
  if (leanHoverKey !== key) return;
  const popup = leanInfoPopup();
  if (state.leanHoverCache[key]) {
    if (!state.leanHoverCache[key].text) {
      hideLeanInfoPopup();
      return;
    }
    setSourceHoverHighlight(btn, column, state.leanHoverCache[key].range);
    popup.classList.remove("hidden");
    popup.innerHTML = renderLeanHoverPopup(state.leanHoverCache[key]);
    positionLeanInfoPopup(btn, pointer);
    return;
  }
  const data = await leanApi("/api/lean/hover", {
    proposition_id: propId,
    method_id: methodId,
    file_path: filePath,
    line,
    column,
  });
  state.leanHoverCache[key] = data;
  if (leanHoverKey !== key) return;
  if (!data.text) {
    hideLeanInfoPopup();
    return;
  }
  setSourceHoverHighlight(btn, column, data.range);
  popup.classList.remove("hidden");
  popup.innerHTML = renderLeanHoverPopup(data);
  positionLeanInfoPopup(btn, pointer);
}

function queueLeanPanelHover(fragment, event) {
  const active = stateForElement(fragment) || state.activeLeanState;
  const infoRef = decodeAttrJson(fragment.dataset.infoRef);
  if (!active?.data?.rpcSessionId || !infoRef) return;
  const pointer = { clientX: event.clientX, clientY: event.clientY };
  const refKey = JSON.stringify(infoRef);
  const key = `panel::${active.propId}::${active.methodId}::${active.filePath}::${active.data.rpcSessionId}::${refKey}::${fragment.dataset.subexprPos || ""}`;
  clearTimeout(leanHoverHideTimer);
  leanHoverKey = key;
  if (state.leanHoverCache[key]) {
    showLeanPanelHover(active, infoRef, fragment, pointer, key);
    return;
  }
  const popup = leanInfoPopup();
  popup.classList.remove("hidden");
  positionLeanInfoPopup(fragment, pointer);
  popup.innerHTML = `<div class="popup-doc">Loading Lean hover...</div>`;
  scheduleLeanHover(() => {
    showLeanPanelHover(active, infoRef, fragment, pointer, key).catch((err) => {
      if (isStaleLeanError(err)) return;
      if (leanHoverKey !== key) return;
      const popup = leanInfoPopup();
      popup.classList.remove("hidden");
      positionLeanInfoPopup(fragment, pointer);
      popup.innerHTML = `<div class="popup-doc">${escapeHtml(err.message)}</div>`;
    });
  });
}

function decodeAttrJson(value) {
  if (!value) return null;
  try {
    return JSON.parse(decodeURIComponent(value));
  } catch (_) {
    return null;
  }
}

async function showLeanPanelHover(active, infoRef, fragment, pointer, key) {
  if (leanHoverKey !== key) return;
  const popup = leanInfoPopup();
  positionLeanInfoPopup(fragment, pointer);
  popup.classList.remove("hidden");
  if (state.leanHoverCache[key]) {
    popup.innerHTML = renderLeanInfoHoverPopup(state.leanHoverCache[key]);
    return;
  }
  popup.innerHTML = `<div class="popup-doc">Loading Lean hover...</div>`;
  const data = await leanApi("/api/lean/info-hover", {
    proposition_id: active.propId,
    method_id: active.methodId,
    file_path: active.filePath,
    line: active.line,
    column: active.column,
    rpc_session_id: active.data.rpcSessionId,
    info_ref: infoRef,
  });
  state.leanHoverCache[key] = data;
  if (leanHoverKey !== key) return;
  positionLeanInfoPopup(fragment, pointer);
  popup.innerHTML = renderLeanInfoHoverPopup(data);
}

function hideLeanInfoPopup() {
  clearTimeout(leanHoverTimer);
  clearTimeout(leanHoverHideTimer);
  leanHoverTimer = null;
  leanHoverPending = null;
  leanHoverKey = "";
  clearSourceHoverHighlight();
  leanInfoPopup().classList.add("hidden");
}

function scheduleLeanHover(callback) {
  leanHoverPending = callback;
  if (leanHoverTimer) return;
  leanHoverTimer = setTimeout(() => {
    const pending = leanHoverPending;
    leanHoverTimer = null;
    leanHoverPending = null;
    if (pending) pending();
  }, 120);
}

function scheduleLeanInfoPopupHide(event) {
  const related = event?.relatedTarget;
  if (related?.closest?.("#leanInfoPopup, .lean-hover-fragment")) return;
  const point = typeof event?.clientX === "number"
    ? { x: event.clientX, y: event.clientY }
    : null;
  clearTimeout(leanHoverHideTimer);
  leanHoverHideTimer = setTimeout(() => {
    const atPointer = point ? document.elementFromPoint(point.x, point.y) : null;
    if (atPointer?.closest?.("#leanInfoPopup, .lean-hover-fragment")) return;
    hideLeanInfoPopup();
  }, 45);
}

function renderLeanInfoView(data) {
  const interactiveMessages = data.interactiveMessages || [];
  const fileMessages = data.messages || [];
  const goals = data.goals || [];
  const rpcErrors = data.rpcErrors || [];
  const statusLabel = data.mode === "rpc"
    ? `${goals.length ? `${goals.length} goal${goals.length === 1 ? "" : "s"}` : "No goals"}`
    : "Diagnostics fallback";
  return `
    <div class="infoview">
      <div class="infoview-status">
        <span class="status-dot ${data.mode === "rpc" ? "ok" : "warn"}"></span>
        <strong>${escapeHtml(statusLabel)}</strong>
        <span>${escapeHtml(data.file || "")}:${data.line}:${data.column ?? 0}</span>
      </div>
      <div class="infoview-tabs">
        <details class="infoview-tab" open>
          <summary>Goals <span>${goals.length}</span></summary>
          ${leanGoalsHtml(goals, data.goal)}
        </details>
        <details class="infoview-tab" ${data.termGoal ? "open" : ""}>
          <summary>Expected Type <span>${data.termGoal ? 1 : 0}</span></summary>
          ${leanTermGoalHtml(data.termGoal)}
        </details>
        <details class="infoview-tab" ${interactiveMessages.length ? "open" : ""}>
          <summary>Messages ${diagnosticTallyHtml(interactiveMessages)}</summary>
          ${leanMessageHtml(interactiveMessages)}
        </details>
        <details class="infoview-tab" ${fileMessages.length ? "open" : ""}>
          <summary>File Diagnostics ${diagnosticTallyHtml(fileMessages)}</summary>
          ${leanMessageHtml(fileMessages)}
        </details>
        <details class="infoview-tab" ${rpcErrors.length ? "open" : ""}>
          <summary>RPC Status <span>${rpcErrors.length}</span></summary>
          ${leanRpcErrorsHtml(rpcErrors)}
        </details>
      </div>
      ${data.note ? `<p class="infoview-note">${escapeHtml(data.note)}</p>` : ""}
    </div>
  `;
}

function renderLeanStateBlock(item) {
  return `
    <section class="lean-state-view" data-lean-state-key="${escapeHtml(item.key)}">
      ${renderLeanInfoView(item.data)}
    </section>
  `;
}

function renderLeanPanel() {
  const current = state.activeLeanData;
  if (!current) {
    $("leanContent").innerHTML = `<p class="subtle">Select a Lean line to inspect live tactic state and diagnostics.</p>`;
    return;
  }
  $("leanContent").innerHTML = renderLeanStateBlock(current);
  bindLeanStateActions();
}

function leanWarmKey(prop) {
  if (!prop) return "";
  const files = ["leaneuclid", "new_method"]
    .map((methodId) => {
      const file = prop.methods[methodId]?.files?.[0];
      return file ? { method_id: methodId, file_path: file.path } : null;
    })
    .filter(Boolean);
  return `${prop.id}::${files.map((f) => `${f.method_id}:${f.file_path}`).join("|")}`;
}

function renderLeanWarmStatus() {
  const box = $("leanWarmStatus");
  if (!box) return;
  const status = state.warm[state.currentWarmKey];
  if (status === "warming") {
    box.className = "lean-warm-status warming";
    box.textContent = "Lean is warming up. Estimated wait: about 5-30 seconds on first load; usually under a second when cached.";
  } else if (status === "partial") {
    box.className = "lean-warm-status warming";
    box.textContent = "Some Lean files are warmed; another file is still unavailable or slow. You can inspect warmed files now.";
  } else if (status === "failed") {
    box.className = "lean-warm-status failed";
    box.textContent = "Lean warm-up failed. Clicking a line will still try a live query, but it may be slow or fail.";
  } else {
    box.className = "lean-warm-status hidden";
    box.textContent = "";
  }
}

function tacticStateText(data) {
  if (!data?.goals?.length) return data?.goal || "No goals.";
  const goals = orderedGoals(data.goals);
  return goals.map((goal, idx) => {
    const lines = [];
    if (goal.userName) lines.push(`case ${goal.userName}`);
    for (const hyp of visibleHyps(goal)) {
      const value = hyp.value ? ` := ${hyp.value}` : "";
      lines.push(`${(hyp.names || []).join(" ")} : ${hyp.type || ""}${value}`);
    }
    const hidden = hiddenHypCount(goal);
    if (hidden) lines.push(`-- ${hidden} hidden local hypoth${hidden === 1 ? "esis" : "eses"}`);
    lines.push(`${goal.goalPrefix || "⊢ "}${goal.target || ""}`);
    return goals.length > 1 ? `-- Goal ${idx + 1}\n${lines.join("\n")}` : lines.join("\n");
  }).join("\n\n");
}

async function copyActiveLeanState() {
  const data = state.activeLeanData?.data;
  if (!data) return;
  await navigator.clipboard.writeText(tacticStateText(data));
}

async function refreshActiveLeanState() {
  if (!state.activeLine) return;
  const { propId, methodId, filePath, line, column } = state.activeLine;
  await inspectLeanLine(propId, methodId, filePath, line, findRenderedCodeLine(methodId, filePath, line), column, { force: true });
}

function setActiveLeanCursor(propId, methodId, filePath, line, btn, column = 0) {
  const previous = state.activeLine;
  const selectedColumn = clampLeanColumn(btn, column);
  document.querySelectorAll(".code-line.active").forEach((el) => el.classList.remove("active"));
  state.activeLine = { propId, methodId, filePath, line, column: selectedColumn };
  if (previous) {
    const previousBtn = findRenderedCodeLine(previous.methodId, previous.filePath, previous.line);
    if (previousBtn && previousBtn !== btn) renderCodeLineSource(previous.methodId, previousBtn);
  }
  btn?.classList.add("active");
  if (btn) renderCodeLineSource(methodId, btn);
  btn?.blur();
  $("leanTitle").textContent = `${filePath}:${line}:${selectedColumn}`;
  return selectedColumn;
}

function leanStateCacheKey(propId, methodId, filePath, line, column) {
  return `${propId}::${methodId}::${filePath}::${line}::${column}`;
}

function leanLineMetaMatches(meta, line) {
  return Boolean(
    meta &&
    line &&
    meta.propId === line.propId &&
    meta.methodId === line.methodId &&
    meta.filePath === line.filePath &&
    Number(meta.line) === Number(line.line) &&
    Number(meta.column ?? 0) === Number(line.column ?? 0)
  );
}

function retryActiveLeanLineAfterWarmup(key, propId, navSeq) {
  if (state.currentWarmKey !== key || state.current?.id !== propId || navSeq !== state.navSeq) return;
  const active = state.activeLine;
  if (!active || active.propId !== propId) return;
  if (leanLineMetaMatches(state.activeLeanData, active)) return;
  const cacheKey = leanStateCacheKey(active.propId, active.methodId, active.filePath, active.line, active.column);
  const cached = state.leanStateCache[cacheKey];
  if (cached) {
    activateLeanState(cached.meta, cached.data);
    return;
  }
  inspectLeanLine(
    active.propId,
    active.methodId,
    active.filePath,
    active.line,
    findRenderedCodeLine(active.methodId, active.filePath, active.line),
    active.column,
    { force: true, navSeq }
  ).catch((err) => {
    if (!isStaleLeanError(err)) console.warn("Lean line query after warm-up failed", err);
  });
}

function activateLeanState(meta, data) {
  const key = registerLeanState(meta, data);
  state.activeLeanState = state.leanStates[key];
  state.activeLeanData = { key, ...state.activeLeanState };
  renderLeanPanel();
}

async function inspectLeanLine(propId, methodId, filePath, line, btn, column = 0, options = {}) {
  clearTimeout(leanCursorQueryTimer);
  const selectedColumn = setActiveLeanCursor(propId, methodId, filePath, line, btn, column);
  state.activeLeanState = null;
  state.activeLeanData = null;
  setLeanCollapsed(false);
  $("leanPanel").classList.add("open");
  $("leanTitle").textContent = `${filePath}:${line}:${selectedColumn}`;
  const cacheKey = leanStateCacheKey(propId, methodId, filePath, line, selectedColumn);
  if (!options.force && state.leanStateCache[cacheKey]) {
    const cached = state.leanStateCache[cacheKey];
    activateLeanState(cached.meta, cached.data);
    return;
  }
  const warming = state.warm[state.currentWarmKey] === "warming";
  $("leanContent").innerHTML = `<p class="subtle">${warming ? "Lean is warming up; this line query may take about 5-30 seconds." : "Querying Lean..."}</p>`;
  let controller = null;
  try {
    if (leanStateController) leanStateController.abort();
    const requestSeq = ++leanStateSeq;
    controller = new AbortController();
    leanStateController = controller;
    leanControllers.add(controller);
    const data = await api("/api/lean/state", {
      method: "POST",
      signal: controller.signal,
      body: JSON.stringify({
        client_id: leanClientId(),
        proposition_id: propId,
        method_id: methodId,
        file_path: filePath,
        line,
        column: selectedColumn,
      }),
    });
    const meta = { propId, methodId, filePath, line: data.line ?? line, column: data.column ?? selectedColumn, rpcSessionId: data.rpcSessionId };
    state.leanStateCache[cacheKey] = { meta, data };
    if (requestSeq !== leanStateSeq) return;
    if (state.navSeq !== options.navSeq && options.navSeq !== undefined) return;
    if (state.current?.id !== propId) return;
    activateLeanState(meta, data);
  } catch (err) {
    if (isStaleLeanError(err) || state.current?.id !== propId) return;
    $("leanContent").innerHTML = `<div class="message error">${escapeHtml(err.message)}</div>`;
  } finally {
    if (controller) {
      leanControllers.delete(controller);
      if (leanStateController === controller) leanStateController = null;
    }
  }
}

function leanLineButtons(methodId, filePath) {
  return Array.from(document.querySelectorAll(`.code-line[data-method="${methodId}"]`))
    .filter((el) => el.dataset.file === filePath);
}

function scheduleLeanCursorQuery(delay = 180) {
  if (!state.activeLine) return;
  clearTimeout(leanCursorQueryTimer);
  const active = { ...state.activeLine };
  leanCursorQueryTimer = setTimeout(() => {
    if (
      !state.activeLine ||
      state.activeLine.propId !== active.propId ||
      state.activeLine.methodId !== active.methodId ||
      state.activeLine.filePath !== active.filePath ||
      Number(state.activeLine.line) !== Number(active.line) ||
      Number(state.activeLine.column) !== Number(active.column)
    ) return;
    inspectLeanLine(
      active.propId,
      active.methodId,
      active.filePath,
      active.line,
      findRenderedCodeLine(active.methodId, active.filePath, active.line),
      active.column,
      { navSeq: state.navSeq }
    );
  }, delay);
}

function moveLeanLine(delta, query = true) {
  if (!state.activeLine) return false;
  const lines = leanLineButtons(state.activeLine.methodId, state.activeLine.filePath);
  if (!lines.length) return false;
  const current = lines.findIndex((el) => Number(el.dataset.line) === Number(state.activeLine.line));
  const next = lines[current + delta];
  if (!next) return false;
  next.scrollIntoView({ block: "center" });
  const selectedColumn = clampLeanColumn(next, state.activeLine.column ?? defaultLeanColumn(next));
  setActiveLeanCursor(
    state.activeLine.propId,
    state.activeLine.methodId,
    state.activeLine.filePath,
    Number(next.dataset.line),
    next,
    selectedColumn
  );
  if (query) scheduleLeanCursorQuery();
  return true;
}

function moveLeanColumn(delta) {
  if (!state.activeLine) return false;
  const btn = findRenderedCodeLine(state.activeLine.methodId, state.activeLine.filePath, state.activeLine.line);
  if (!btn) return false;
  const nextColumn = clampLeanColumn(btn, Number(state.activeLine.column || 0) + delta);
  if (nextColumn === Number(state.activeLine.column || 0)) return true;
  setActiveLeanCursor(state.activeLine.propId, state.activeLine.methodId, state.activeLine.filePath, state.activeLine.line, btn, nextColumn);
  scheduleLeanCursorQuery();
  return true;
}

function shouldIgnoreArrowNavigation(event) {
  const target = event.target;
  if (!target) return false;
  const tag = target.tagName?.toLowerCase();
  return tag === "input" || tag === "textarea" || tag === "select" || target.isContentEditable;
}

function warmFilesForProp(prop) {
  return ["leaneuclid", "new_method"]
    .map((methodId) => {
      const file = prop.methods[methodId]?.files?.[0];
      return file ? { method_id: methodId, file_path: file.path } : null;
    })
    .filter(Boolean);
}

async function requestLeanWarmup(prop, navSeq) {
  const key = leanWarmKey(prop);
  const files = warmFilesForProp(prop);
  if (!files.length || state.warm[key] === "ready" || state.warm[key] === "warming") return;
  for (const warmKey of Object.keys(state.warm)) {
    if (warmKey !== key && (state.warm[warmKey] === "ready" || state.warm[warmKey] === "warming")) {
      state.warm[warmKey] = "idle";
    }
  }
  state.warm[key] = "warming";
  if (state.currentWarmKey === key) renderLeanWarmStatus();
  try {
    const data = await api("/api/lean/warm", {
      method: "POST",
      body: JSON.stringify({ client_id: leanClientId(), reviewer_token: reviewerToken(), proposition_id: prop.id, files }),
    });
    if (!data.request_id) {
      state.warm[key] = data.ok === false ? "failed" : "ready";
      if (state.currentWarmKey === key) renderLeanWarmStatus();
      return;
    }
    state.warmRequests[key] = data.request_id;
    pollLeanWarmup(key, data.request_id, navSeq, prop.id);
  } catch (err) {
    state.warm[key] = "failed";
    console.warn("Lean warm-up request failed", err);
    if (state.currentWarmKey === key) renderLeanWarmStatus();
  }
}

function pollLeanWarmup(key, requestId, navSeq, propId) {
  setTimeout(async () => {
    if (state.warmRequests[key] !== requestId || state.warm[key] !== "warming") return;
    try {
      const data = await api("/api/lean/warm-status", {
        method: "POST",
        body: JSON.stringify({ client_id: leanClientId(), request_id: requestId }),
      });
      if (data.status === "ready" || data.status === "partial") {
        state.warm[key] = data.status;
        retryActiveLeanLineAfterWarmup(key, propId, navSeq);
      } else if (data.status === "failed") {
        state.warm[key] = "failed";
      } else if (data.status === "skipped") {
        state.warm[key] = "idle";
      } else {
        pollLeanWarmup(key, requestId, navSeq, propId);
      }
    } catch (err) {
      state.warm[key] = "failed";
      console.warn("Lean warm-up status failed", err);
    } finally {
      if (state.currentWarmKey === key && state.current?.id === propId && navSeq === state.navSeq) {
        renderLeanWarmStatus();
      }
    }
  }, 1200);
}

function renderStagePanel(prop) {
  const stage = stageForProp(prop);
  const canReview = canReviewProp(prop);
  const currentMethodId = stageMethodId(prop);
  const propDraftOrSavedComplete = canReview
    && ["leaneuclid", "new_method"].every((methodId) => methodDraftOrSavedScored(prop.id, methodId))
    && preferencesDraftOrSavedComplete(prop.id);
  const guideNextQuestion = canReview
    && stage !== "compare"
    && currentMethodId
    && methodDraftOrSavedScored(prop.id, currentMethodId);
  const guideNextProposition = canReview
    && stage === "compare"
    && propDraftOrSavedComplete;
  $("prevProp")?.toggleAttribute("disabled", stage === "A");
  $("nextProp")?.toggleAttribute("disabled", stage === "compare");
  $("nextAssignedProp")?.toggleAttribute("disabled", !propDraftOrSavedComplete);
  $("prevProp")?.setAttribute("title", "Previous question");
  $("nextProp")?.setAttribute("title", "Next question");
  $("prevProp")?.setAttribute("aria-label", "Previous question");
  $("nextProp")?.setAttribute("aria-label", "Next question");
  $("nextProp")?.classList.toggle("attention", guideNextQuestion);
  $("nextAssignedProp")?.classList.toggle("attention", guideNextProposition);
}

function moveStage(delta) {
  const prop = state.current;
  if (!prop) return;
  const stages = ["A", "B", "compare"];
  const idx = stages.indexOf(stageForProp(prop));
  const next = stages[Math.max(0, Math.min(stages.length - 1, idx + delta))];
  if (next && next !== stageForProp(prop)) setStage(prop, next);
}

function applyStageLayout(prop) {
  const stage = stageForProp(prop);
  const grid = document.querySelector(".formalization-grid");
  const reading = document.querySelector(".reading-grid");
  const workspace = $("reviewWorkspace");
  if (!grid || !reading) return;
  workspace?.classList.toggle("method-stage", stage !== "compare");
  workspace?.classList.toggle("comparison-stage", stage === "compare");
  workspace?.classList.toggle("comparison-reading-collapsed", stage === "compare" && state.comparisonCollapsed.reading);
  workspace?.classList.toggle("comparison-code-collapsed", stage === "compare" && state.comparisonCollapsed.code);
  grid.classList.toggle("single-method-stage", stage !== "compare");
  grid.classList.toggle("comparison-stage", stage === "compare");
  reading.classList.toggle("method-stage-reading", stage !== "compare");
  reading.classList.toggle("comparison-stage-reading", stage === "compare");
  $("toggleComparisonReading")?.classList.toggle("hidden", stage !== "compare");
  $("toggleComparisonCode")?.classList.toggle("hidden", stage !== "compare");
  $("toggleText")?.classList.toggle("hidden", stage === "compare");
  if (stage === "compare") {
    $("nlText")?.classList.remove("compact");
    if ($("toggleText")) $("toggleText").textContent = "Compact";
  }
  updateComparisonCollapseControls(stage === "compare");
  const activeSlot = stage === "compare" ? "" : stage;
  for (const slot of ["A", "B"]) {
    const panel = methodPanelForSlot(slot);
    panel?.classList.toggle("stage-hidden", Boolean(activeSlot && slot !== activeSlot));
  }
  setupMethodStageHeightSync(stage !== "compare");
}

function setupMethodStageHeightSync(enabled) {
  if (methodStageResizeObserver) {
    methodStageResizeObserver.disconnect();
    methodStageResizeObserver = null;
  }
  const workspace = $("reviewWorkspace");
  if (!workspace) return;
  if (!enabled) {
    workspace.style.removeProperty("--method-stage-height");
    return;
  }
  const reading = workspace.querySelector(".reading-grid");
  if (!reading) return;
  const update = () => syncMethodStageHeight();
  methodStageResizeObserver = new ResizeObserver(update);
  methodStageResizeObserver.observe(reading);
  requestAnimationFrame(update);
}

function syncMethodStageHeight() {
  const workspace = $("reviewWorkspace");
  const reading = workspace?.querySelector(".reading-grid");
  if (!workspace || !reading || !workspace.classList.contains("method-stage")) return;
  const height = Math.ceil(reading.getBoundingClientRect().height);
  if (height > 0) workspace.style.setProperty("--method-stage-height", `${height}px`);
}

function renderCurrent() {
  const prop = state.current;
  if (!prop) return;
  history.replaceState(null, "", `#/${prop.id}`);
  if (!state.reviewStageByProp[prop.id]) setStageForProp(prop, recommendedStage(prop));
  if (stageForProp(prop) === "compare") {
    state.comparisonCollapsed.reading = true;
    state.comparisonCollapsed.code = true;
  }
  $("propKicker").textContent = prop.display;
  state.activeLine = null;
  state.activeLeanState = null;
  state.activeLeanData = null;
  state.leanStates = {};
  state.openFiles = {};
  state.externalFiles = {};
  state.activeFiles = {};
  hideLineMappingPopup();
  state.currentWarmKey = leanWarmKey(prop);
  renderLeanWarmStatus();
  renderLeanPanel();
  const slots = methodSlotOrder(prop);
  $("methodALabel").textContent = "Formalization A";
  $("methodBLabel").textContent = "Formalization B";
  $("methodAPath").textContent = "";
  $("methodBPath").textContent = "";
  for (const { slot, methodId } of slots) {
    const panel = methodPanelForSlot(slot);
    const toggle = methodToggleForSlot(slot);
    if (panel) {
      panel.dataset.method = methodId;
      panel.dataset.slot = slot;
    }
    if (toggle) toggle.dataset.toggleMethod = methodId;
  }
  const pairReady = prop.methods.leaneuclid.available && prop.methods.new_method.available;
  const assigned = isAssigned(prop.id);
  const banner = $("availabilityBanner");
  banner.classList.toggle("hidden", pairReady && assigned);
  banner.textContent = !pairReady
    ? "One formalization is not available for this proposition yet. You can preview the available material, but scoring is disabled until both formalizations exist."
    : (!assigned ? "This proposition is available for browsing, but it is not part of your assigned review set. Scoring is disabled here." : "");
  renderText(prop);
  renderDiagram(prop);
  renderCode($("methodACode"), prop, methodIdForSlot("A", prop));
  renderCode($("methodBCode"), prop, methodIdForSlot("B", prop));
  renderMethodCollapseState();
  applyStageLayout(prop);
  renderStagePanel(prop);
  renderMetricCards(prop);
  renderPropList();
  setSaveStatus(reviewerToken() ? "Autosave ready" : "Open your email link", reviewerToken() ? "" : "error");
  requestLeanWarmup(prop, state.navSeq);
}

async function selectProp(propId) {
  const navSeq = ++state.navSeq;
  const previousProp = state.current;
  if (previousProp && autosaveTimer) {
    clearTimeout(autosaveTimer);
    autosaveTimer = null;
    saveResponseFor(previousProp, { silent: true }).catch((err) => {
      console.warn("Autosave before navigation failed", err);
      setSaveStatus("Save failed", "error");
    });
  }
  if (propFetchController) propFetchController.abort();
  abortLeanRequests();
  propFetchController = new AbortController();
  state.currentId = propId;
  renderPropList();
  $("propKicker").textContent = "Loading...";
  try {
    const prop = await api(`/api/propositions/${encodeURIComponent(propId)}`, { signal: propFetchController.signal });
    if (navSeq !== state.navSeq || propId !== state.currentId) return;
    state.current = prop;
  } catch (err) {
    if (err.name === "AbortError") return;
    if (navSeq !== state.navSeq) return;
    $("availabilityBanner").classList.remove("hidden");
    $("availabilityBanner").textContent = `Failed to load proposition: ${err.message}`;
    return;
  }
  renderCurrent();
}

async function loadProgress() {
  if (!reviewerToken()) return;
  state.progress = await api(`/api/progress-token/${encodeURIComponent(reviewerToken())}`);
  renderPropList();
  if (state.current) {
    renderMetricCards(state.current);
    renderStagePanel(state.current);
  }
}

function setSaveStatus(text, kind = "") {
  const el = $("saveStatus");
  if (!el) return;
  el.textContent = text;
  el.className = `save-status ${kind}`.trim();
}

function responsePayloadFor(prop) {
  if (!prop) return null;
  const scores = [];
  for (const methodId of ["leaneuclid", "new_method"]) {
    if (!prop.methods[methodId].available) continue;
    for (const metric of state.config.rubric.metrics) {
      const score = getScore(prop.id, methodId, metric.id);
      if (score === null) continue;
      scores.push({
        method_id: methodId,
        metric_id: metric.id,
        score,
        note: getNote(prop.id, methodId, metric.id),
      });
    }
  }
  const preferences = [];
  for (const question of preferenceQuestions()) {
    const choice = getPreference(prop.id, question.id);
    if (choice === null) continue;
    preferences.push({
      question_id: question.id,
      choice,
      choice_basis: "method",
      negative_method_id: "leaneuclid",
      positive_method_id: "new_method",
    });
  }
  return {
    proposition_id: prop.id,
    scores,
    preferences,
    overall_note: getOverallNote(prop.id),
  };
}

function showCompletionNotice(propId) {
  state.completedNoticePropId = propId;
  const notice = $("completionNotice");
  if (notice) {
    notice.textContent = allAssignedPropsDone()
      ? "All assigned propositions are complete. You can still revisit any proposition and modify your answers if needed."
      : "Proposition review complete. Next proposition is ready.";
    notice.classList.remove("hidden");
    notice.classList.remove("pulse");
    requestAnimationFrame(() => notice.classList.add("pulse"));
  }
  $("nextAssignedProp")?.classList.add("attention");
  window.setTimeout(() => {
    if (state.completedNoticePropId !== propId) return;
    notice?.classList.add("hidden");
  }, 4200);
}

function commitSavedProgress(propId, scores, preferences, overallNote, wasDone = false) {
  state.progress.responses = state.progress.responses.filter((r) => r.proposition_id !== propId);
  for (const item of scores) {
    state.progress.responses.push({
      proposition_id: propId,
      method_id: item.method_id,
      metric_id: item.metric_id,
      score: item.score,
      note: item.note || "",
    });
  }
  state.progress.preferences = (state.progress.preferences || []).filter((r) => r.proposition_id !== propId);
  for (const item of preferences) {
    state.progress.preferences.push({
      proposition_id: propId,
      question_id: item.question_id,
      choice: item.choice,
    });
  }
  state.progress.overall_notes = state.progress.overall_notes.filter((n) => n.proposition_id !== propId);
  if (overallNote) {
    state.progress.overall_notes.push({ proposition_id: propId, note: overallNote });
  }
  if (!wasDone && isDone(propId)) showCompletionNotice(propId);
  renderPropList();
  if (state.current?.id === propId) renderStagePanel(state.current);
}

async function saveResponseFor(prop, options = {}) {
  if (!prop || !reviewerToken()) {
    setSaveStatus("Open your email link", "error");
    return false;
  }
  if (!canReviewProp(prop)) {
    setSaveStatus("Browse only", "error");
    return false;
  }
  const payload = responsePayloadFor(prop);
  if (!payload) return false;
  const wasDone = isDone(prop.id);
  const seq = ++autosaveSeq;
  if (!options.silent) setSaveStatus("Saving...", "saving");
  else setSaveStatus("Saving...", "saving");
  await api("/api/responses", {
    method: "POST",
    body: JSON.stringify({
      reviewer_token: reviewerToken(),
      proposition_id: payload.proposition_id,
      scores: payload.scores,
      preferences: payload.preferences,
      overall_note: payload.overall_note,
    }),
  });
  if (seq === autosaveSeq) setSaveStatus("Saved");
  commitSavedProgress(payload.proposition_id, payload.scores, payload.preferences, payload.overall_note, wasDone);
  return true;
}

function scheduleAutosave(prop = state.current, delay = 700) {
  clearTimeout(autosaveTimer);
  if (!prop) return;
  setSaveStatus(reviewerToken() ? "Unsaved" : "Open your email link", reviewerToken() ? "" : "error");
  autosaveTimer = setTimeout(() => {
    saveResponseFor(prop, { silent: true }).catch((err) => {
      console.warn("Autosave failed", err);
      setSaveStatus("Save failed", "error");
    });
  }, delay);
}

function moveProp(delta) {
  const idx = state.props.findIndex((p) => p.id === state.currentId);
  const next = state.props[idx + delta];
  if (next) selectProp(next.id);
}

function moveAssignedProp(delta = 1) {
  const props = assignedProps();
  if (!props.length) return;
  const idx = props.findIndex((p) => p.id === state.currentId);
  const next = props[((idx < 0 ? -1 : idx) + delta + props.length) % props.length];
  if (next) selectProp(next.id);
}

function setSidebarCollapsed(collapsed) {
  const wasCollapsed = state.sidebarCollapsed;
  state.sidebarCollapsed = collapsed;
  localStorage.setItem("survey.sidebarCollapsed", String(collapsed));
  $("app").classList.toggle("sidebar-collapsed", collapsed);
  $("showSidebar").classList.toggle("hidden", !collapsed);
  $("toggleSidebar").setAttribute("aria-expanded", String(!collapsed));
  if (wasCollapsed && !collapsed) keepActivePropInView();
}

function setLeanCollapsed(collapsed) {
  state.leanCollapsed = collapsed;
  localStorage.setItem("survey.leanCollapsed", String(collapsed));
  $("app").classList.toggle("lean-collapsed", collapsed);
  $("showLean").classList.toggle("hidden", !collapsed);
  $("toggleLean").setAttribute("aria-expanded", String(!collapsed));
  if (collapsed) $("leanPanel").classList.remove("open");
}

function setComparisonCollapsed(group, collapsed) {
  if (!Object.prototype.hasOwnProperty.call(state.comparisonCollapsed, group)) return;
  state.comparisonCollapsed[group] = Boolean(collapsed);
  applyStageLayout(state.current);
}

function updateComparisonCollapseControls(isComparison = stageForProp(state.current) === "compare") {
  const readingCollapsed = Boolean(state.comparisonCollapsed.reading);
  const codeCollapsed = Boolean(state.comparisonCollapsed.code);
  const readingButton = $("toggleComparisonReading");
  const codeButton = $("toggleComparisonCode");
  if (readingButton) {
    readingButton.title = `${readingCollapsed ? "Expand" : "Collapse"} textbook and diagram`;
    readingButton.setAttribute("aria-label", readingButton.title);
    readingButton.setAttribute("aria-expanded", String(isComparison && !readingCollapsed));
  }
  if (codeButton) {
    codeButton.title = `${codeCollapsed ? "Expand" : "Collapse"} formalizations`;
    codeButton.setAttribute("aria-label", codeButton.title);
    codeButton.setAttribute("aria-expanded", String(isComparison && !codeCollapsed));
  }
}

function renderMethodCollapseState() {
  const slots = methodSlotOrder(state.current);
  for (const { slot, methodId } of slots) {
    const panel = methodPanelForSlot(slot);
    const toggle = methodToggleForSlot(slot);
    const label = `Formalization ${slot}`;
    panel?.classList.remove("collapsed");
    if (!toggle) continue;
    toggle.classList.add("hidden");
    toggle.textContent = "−";
    toggle.title = `${label} panel`;
    toggle.setAttribute("aria-label", toggle.title);
    toggle.setAttribute("aria-expanded", "true");
  }
}

async function enterReviewSession(token) {
  const clean = String(token || "").trim();
  setGateMessage("Checking your personal link...");
  if (!await reviewerTokenExists(clean)) {
    localStorage.removeItem("survey.reviewerToken");
    state.reviewerToken = "";
    setGateMessage("This survey link is invalid or disabled. Please request a new email link.", "error");
    $("welcomeGate").classList.remove("hidden");
    $("app").classList.add("hidden");
    return false;
  }
  state.reviewerToken = clean;
  localStorage.setItem("survey.reviewerToken", clean);
  $("reviewerCode").value = "";
  await loadProgress();
  const tutorialCompleted = await loadTutorialStatus();
  $("welcomeGate").classList.add("hidden");
  $("app").classList.remove("hidden");
  setSidebarCollapsed(state.sidebarCollapsed);
  setLeanCollapsed(state.leanCollapsed);
  renderMethodCollapseState();
  const assignedInitial = assignedProps()[0]?.id;
  const initial = location.hash.replace(/^#\/?/, "") || assignedInitial || state.props.find(ready)?.id || state.props[0]?.id;
  renderPropList();
  if (!state.current && initial) await selectProp(initial);
  if (!tutorialCompleted) openTutorial();
  setGateMessage("");
  return true;
}

async function sendReviewerLinkFromGate() {
  const email = $("gateEmail").value.trim();
  if (!email) {
    setGateMessage("Enter your email address.", "error");
    $("gateEmail").focus();
    return false;
  }
  setGateMessage("Sending your personal survey link...");
  $("enterReview").disabled = true;
  try {
    await requestReviewerLink(email);
    $("gateEmail").value = "";
    setGateMessage("A personal survey link has been sent to that email address. Please check your inbox.", "success");
    return true;
  } catch (err) {
    setGateMessage(err.message, "error");
    return false;
  } finally {
    $("enterReview").disabled = false;
  }
}

async function init() {
  state.config = await api("/api/config");
  state.props = await api("/api/propositions");

  $("reviewerGateForm").addEventListener("submit", async (event) => {
    event.preventDefault();
    await sendReviewerLinkFromGate();
  });
  $("searchBox").addEventListener("input", (e) => {
    state.search = e.target.value;
    renderPropList();
  });
  document.querySelectorAll(".seg").forEach((btn) => {
    btn.addEventListener("click", () => {
      document.querySelectorAll(".seg").forEach((b) => b.classList.remove("active"));
      btn.classList.add("active");
      state.filter = btn.dataset.filter;
      renderPropList();
    });
  });
  $("toggleText").addEventListener("click", () => {
    $("nlText").classList.toggle("compact");
    $("toggleText").textContent = $("nlText").classList.contains("compact") ? "Expand" : "Compact";
  });
  $("toggleComparisonReading").addEventListener("click", () => {
    setComparisonCollapsed("reading", !state.comparisonCollapsed.reading);
  });
  $("toggleComparisonCode").addEventListener("click", () => {
    setComparisonCollapsed("code", !state.comparisonCollapsed.code);
  });
  $("nlText").addEventListener("click", (event) => {
    const propButton = event.target.closest?.("[data-prop-ref]");
    if (propButton) {
      hideTextReferencePopup();
      selectProp(propButton.dataset.propRef);
      return;
    }
    const refButton = event.target.closest?.("[data-ref-id]");
    if (refButton) {
      showTextReference(refButton.dataset.refId, refButton);
      return;
    }
  });
  document.addEventListener("click", (event) => {
    if (event.target.closest?.("#textReferencePopup, .text-ref")) return;
    hideTextReferencePopup();
  });
  $("prevProp").addEventListener("click", () => moveStage(-1));
  $("nextProp").addEventListener("click", () => moveStage(1));
  $("nextAssignedProp").addEventListener("click", () => moveAssignedProp(1));
  $("toggleSidebar").addEventListener("click", () => setSidebarCollapsed(true));
  $("showSidebar").addEventListener("click", () => setSidebarCollapsed(false));
  $("toggleLean").addEventListener("click", () => setLeanCollapsed(true));
  $("showLean").addEventListener("click", () => {
    setLeanCollapsed(false);
    $("leanPanel").classList.add("open");
  });
  $("tutorialButton").addEventListener("click", () => openTutorial(true));
  $("tutorialSkip").addEventListener("click", () => closeTutorial(true));
  $("tutorialBack").addEventListener("click", previousTutorialStep);
  $("tutorialNext").addEventListener("click", nextTutorialStep);
  window.addEventListener("resize", positionTutorial);
  window.addEventListener("resize", syncMethodStageHeight);
  window.addEventListener("scroll", positionTutorial, true);
  $("leanRefresh").addEventListener("click", refreshActiveLeanState);
  $("leanCopy").addEventListener("click", () => {
    copyActiveLeanState().catch((err) => {
      $("leanContent").insertAdjacentHTML("afterbegin", `<div class="message error">${escapeHtml(err.message)}</div>`);
    });
  });
  document.addEventListener("keydown", (event) => {
    if (event.key === "Control" || event.key === "Meta") refreshCtrlClickAffordance(true);
    if (shouldIgnoreArrowNavigation(event)) return;
    if (event.key === "ArrowDown" && moveLeanLine(1)) {
      event.preventDefault();
    } else if (event.key === "ArrowUp" && moveLeanLine(-1)) {
      event.preventDefault();
    } else if (event.key === "ArrowRight" && moveLeanColumn(1)) {
      event.preventDefault();
    } else if (event.key === "ArrowLeft" && moveLeanColumn(-1)) {
      event.preventDefault();
    }
  });
  document.addEventListener("keyup", (event) => {
    if (event.key === "Control" || event.key === "Meta") refreshCtrlClickAffordance(event.ctrlKey || event.metaKey);
  });
  window.addEventListener("blur", () => {
    clearCtrlClickAffordance();
    lastCodePointer = null;
  });

  const tokenFromHash = inviteTokenFromHash();
  if (tokenFromHash) {
    clearInviteHash();
    const ok = await enterReviewSession(tokenFromHash);
    if (!ok) $("gateEmail").focus();
  } else if (state.reviewerToken) {
    const ok = await enterReviewSession(state.reviewerToken);
    if (!ok) $("gateEmail").focus();
  } else {
    $("welcomeGate").classList.remove("hidden");
    $("app").classList.add("hidden");
    $("gateEmail").focus();
  }
}

init().catch((err) => {
  document.body.innerHTML = `<pre style="padding:20px;color:#8b0000">${escapeHtml(err.stack || err.message)}</pre>`;
});
