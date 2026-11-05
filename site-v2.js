/* Progressive enhancement for the public proof-ledger search.
   The website renders as ordinary HTML without this file or a CDN. */
(() => {
  "use strict";

  const search = document.getElementById("ledger-query");
  const status = document.getElementById("ledger-status");
  const results = document.getElementById("ledger-results");
  const count = document.getElementById("ledger-result-count");
  const more = document.getElementById("ledger-more");
  const message = document.getElementById("ledger-message");
  if (!search || !status || !results || !count || !more || !message) return;

  let all = [];
  let filtered = [];
  let shown = 0;
  const BATCH = 20;
  const STATUS = new Set(["imported", "proved", "open"]);
  const SOURCE = "https://github.com/dovvnloading/loops-research-archive";

  function element(tag, className, text) {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text !== undefined) node.textContent = String(text);
    return node;
  }

  function renderRow(record) {
    const row = element("article", "ledger-item");
    const meta = element("div", "row-meta");
    const heading = element("h4", null, record.id);
    const tag = element("span", "tag tag--" + record.status, record.status);
    const paragraph = element("p", null, record.statement);
    const dependencyCount = Array.isArray(record.deps) ? record.deps.length : 0;
    const details = element(
      "div", "deps",
      "Dependencies: " + (dependencyCount ? record.deps.join(", ") : "none")
    );
    const evidence = element("div", "deps", "Evidence reference: " + (record.evidence || "not specified"));

    meta.append(heading, tag);
    row.append(meta, paragraph, details, evidence);

    const citation = element("a", "small", "Locate claim in GitHub");
    citation.href = SOURCE + "/search?q=" + encodeURIComponent(record.id) + "&type=code";
    citation.target = "_blank";
    citation.rel = "noopener noreferrer";
    citation.setAttribute("aria-label", "Search repository for " + record.id);
    row.append(citation);
    return row;
  }

  function appendRows() {
    const upcoming = filtered.slice(shown, shown + BATCH);
    const fragment = document.createDocumentFragment();
    for (const row of upcoming) fragment.appendChild(renderRow(row));
    results.appendChild(fragment);
    shown += upcoming.length;
    more.hidden = shown >= filtered.length;
    more.disabled = more.hidden;
    count.textContent = filtered.length + " matches · " + shown + " shown";
    if (!filtered.length) {
      results.appendChild(element("p", "ledger-empty", "No obligations match those filters. Try another query or status."));
    }
  }

  function filter() {
    const q = search.value.trim().toLocaleLowerCase();
    const selected = status.value;
    filtered = all.filter((row) => {
      if (selected !== "all" && row.status !== selected) return false;
      if (!q) return true;
      return row.id.toLocaleLowerCase().includes(q)
        || row.statement.toLocaleLowerCase().includes(q)
        || row.deps.join(" ").toLocaleLowerCase().includes(q);
    });
    shown = 0;
    results.replaceChildren();
    appendRows();
  }

  function parseLedger(json) {
    if (!json || !Array.isArray(json.obligations)) throw new Error("Invalid ledger data");
    const rows = json.obligations.map((row) => {
      if (!row || typeof row.id !== "string" || !STATUS.has(row.status)) {
        throw new Error("Unrecognized ledger record");
      }
      return {
        id: row.id,
        status: row.status,
        statement: typeof row.statement === "string" ? row.statement : "",
        deps: Array.isArray(row.deps) ? row.deps.filter((x) => typeof x === "string") : [],
        evidence: typeof row.evidence === "string" ? row.evidence : ""
      };
    });
    return rows;
  }

  search.addEventListener("input", filter);
  status.addEventListener("change", filter);
  more.addEventListener("click", appendRows);

  // The status chart is source-locked. Never silently rewrite it from
  // current JSON data without an explicit new dated status review.
  fetch("./ledger.json", { cache: "no-store" })
    .then((response) => {
      if (!response.ok) throw new Error("HTTP " + response.status);
      return response.json();
    })
    .then((data) => {
      all = parseLedger(data);
      message.hidden = true;
      search.disabled = false;
      status.disabled = false;
      filter();
    })
    .catch(() => {
      message.textContent = "Interactive filtering is unavailable right now. The complete proof ledger remains available as a JSON download and on GitHub.";
      message.hidden = false;
      search.disabled = true;
      status.disabled = true;
      more.hidden = true;
      count.textContent = "Search temporarily unavailable";
    });
})();
