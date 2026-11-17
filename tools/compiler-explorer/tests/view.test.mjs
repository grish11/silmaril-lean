// node --test tools/compiler-explorer/tests/view.test.mjs
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { lineOffsets, fragmentLines, indexEdges, badge, uncovered } from "../ui/view.js";

const root = new URL("../../../", import.meta.url);
const manifest = (name) => JSON.parse(readFileSync(new URL(`examples/compiler-explorer/manifests/${name}.json`, root)));
const text = (path) => readFileSync(new URL(path, root), "utf8");

// The API's shape of a problem, from a manifest and the files it names.
function problemOf(m) {
  const fragments = Object.fromEntries(m.fragments.map((f) => [f.id, f]));
  return { edges: m.edges, fragments, view: m.view, obligations: m.obligations };
}

test("line offsets count UTF-8 bytes", () => {
  assert.deepEqual(lineOffsets("a\nβc\n"), [[0, 1], [2, 5]]);
  assert.deepEqual(lineOffsets("x"), [[0, 1]]);
});

test("a byte fragment covers the lines it overlaps, and only those", () => {
  const lines = lineOffsets("ab\ncd\nef\n");
  assert.deepEqual(fragmentLines({ space: "bytes", ranges: [[3, 5], [6, 8]] }, lines), [2, 3]);
  assert.deepEqual(fragmentLines({ space: "bytes", ranges: [[2, 3]] }, lines), []);
});

test("object-code fragments land on the listing lines of their offsets", () => {
  const m = manifest("compiles-to--straight--O0--add3");
  const p = problemOf(m);
  const src = lineOffsets(text(m.artifacts.source.path));
  const tgt = lineOffsets(text(m.artifacts.listing.path));
  const idx = indexEdges(p, "semantic", src, tgt);
  // point 2 is `int t = s + c;` (line 5): four instructions at 0x18..0x23
  const seg2 = idx.edgeLines.get("seg/add3/2");
  assert.deepEqual(seg2.source, [5]);
  assert.equal(seg2.target.length, 4);
  // every instruction line of add3 is in exactly one semantic segment
  const listed = [...idx.byLine.target.values()];
  assert.equal(listed.length, 16);
  assert.ok(listed.every((ids) => ids.length === 1));
});

test("many-to-many: an inlined line maps to discontiguous assembly", () => {
  const m = manifest("programs--msort--O2");
  const p = problemOf(m);
  const src = lineOffsets(text(m.artifacts.source.path));
  const tgt = lineOffsets(text(m.artifacts.target.path));
  const idx = indexEdges(p, "navigation", src, tgt);
  const l8 = idx.byLine.source.get(8);
  assert.ok(l8.length >= 1);
  const lines = idx.edgeLines.get(l8[0]).target;
  assert.ok(lines.length > 1 && lines.some((n, i) => i > 0 && n !== lines[i - 1] + 1), "not contiguous");
  // the call to the inlined `merge` (line 24) has no instruction of its own
  assert.ok(uncovered(idx, "source", src.length, () => true).includes(24));
});

test("only `proved` is shown as proved", () => {
  assert.equal(badge("proved").label, "proved");
  for (const s of ["open", "unchecked", "rejected", "stale", "unbound", "unsupported", "passed", "kernel", "true", undefined]) {
    assert.notEqual(badge(s).label, "proved", String(s));
    assert.notEqual(badge(s).cls, "st-proved", String(s));
  }
});
