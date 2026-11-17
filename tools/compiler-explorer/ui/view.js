// Pure functions of the compiler explorer's view: no DOM. Tested by tests/view.test.mjs.

/** Byte offset [start, end) of each line of a text (as UTF-8 bytes), lines numbered from 1. */
export function lineOffsets(text) {
  const enc = new TextEncoder();
  const out = [];
  let pos = 0;
  for (const line of text.split("\n")) {
    const n = enc.encode(line).length;
    out.push([pos, pos + n]);
    pos += n + 1;
  }
  if (text.endsWith("\n")) out.pop();
  return out;
}

const overlaps = (a0, a1, b0, b1) => (a0 < b1 && b0 < a1) || (a0 === a1 && b0 <= a0 && a0 < b1);

/** The 1-based display lines a fragment covers. `lines` are the byte ranges of the displayed text;
 * `targetMap` (for the `text-offset` space) lists [offLo, offHi, byteStart, byteEnd] per listing line. */
export function fragmentLines(fragment, lines, targetMap) {
  const out = new Set();
  for (const [lo, hi] of fragment.ranges) {
    if (fragment.space === "bytes") {
      lines.forEach(([s, e], i) => { if (overlaps(lo, hi, s, e)) out.add(i + 1); });
    } else if (fragment.space === "text-offset") {
      for (const [o0, o1, s] of targetMap || []) {
        if (overlaps(lo, hi, o0, o1)) {
          const i = lines.findIndex(([ls]) => ls === s);
          if (i >= 0) out.add(i + 1);
        }
      }
    }
  }
  return [...out].sort((a, b) => a - b);
}

/** Index the edges of one kind: for each side, display line -> edge ids, and edge -> lines.
 * The relation is many-to-many: a line can lie in several edges and an edge spans several lines
 * (on either side, possibly not contiguous). */
export function indexEdges(problem, kind, srcLines, tgtLines) {
  const map = problem.view.target_map;
  const lines = { source: srcLines, target: tgtLines };
  const byLine = { source: new Map(), target: new Map() };
  const edgeLines = new Map();
  for (const e of problem.edges) {
    if (e.kind !== kind) continue;
    const el = { source: new Set(), target: new Set() };
    for (const side of ["source", "target"]) {
      for (const fid of e[side]) {
        const f = problem.fragments[fid];
        if (!f) continue;
        for (const n of fragmentLines(f, lines[side], side === "target" ? map : null)) {
          el[side].add(n);
          if (!byLine[side].has(n)) byLine[side].set(n, []);
          byLine[side].get(n).push(e.id);
        }
      }
    }
    edgeLines.set(e.id, { source: [...el.source].sort((a, b) => a - b), target: [...el.target].sort((a, b) => a - b) });
  }
  return { byLine, edgeLines };
}

/** The obligations attached to an edge (its segment and its C-to-Core point). */
export function edgeObligations(problem, edgeId) {
  return problem.obligations.filter((o) => o.edge === edgeId);
}

/** What a status badge says. Only the server's `proved` is ever shown as proved. */
export function badge(status) {
  const known = {
    proved: ["proved", "checked by Lean's kernel"],
    open: ["open", "stated in Lean, not proved"],
    unchecked: ["unchecked", "a proof is named but no checked evidence is recorded"],
    rejected: ["rejected", "the named proof does not prove this statement"],
    stale: ["stale", "proved only for another version of these artifacts"],
    unsupported: ["unsupported", "not stated: no model covers it"],
    passed: ["test passed", "an execution test, not a proof"],
    failed: ["test failed", "an execution test failed"],
  };
  const [label, title] = known[status] || ["unknown", "no status recorded"];
  return { cls: `st-${known[status] ? status : "unknown"}`, label, title };
}

/** Lines of a side not covered by any edge of a kind (optimized away, generated, unattributed). */
export function uncovered(index, side, count, isCode) {
  const out = [];
  for (let n = 1; n <= count; n++) if (isCode(n) && !index.byLine[side].has(n)) out.push(n);
  return out;
}
