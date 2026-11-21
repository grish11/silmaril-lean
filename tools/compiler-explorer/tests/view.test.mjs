// node --test tools/compiler-explorer/tests/view.test.mjs
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { lineOffsets, fragmentLines, indexEdges, badge, uncovered, includeRows, prettySexp, stageTrust } from "../ui/view.js";

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
  for (const s of ["open", "unchecked", "rejected", "stale", "unbound", "claimed", "unsupported", "passed", "kernel", "true", undefined]) {
    assert.notEqual(badge(s).label, "proved", String(s));
    assert.notEqual(badge(s).cls, "st-proved", String(s));
  }
});

import { highlightLine, langOf } from "../ui/view.js";

test("highlighting keeps every character and never interprets markup", () => {
  const lines = [
    'int *addp(int *p, int *q) { return p + q; } /* <script>alert(1)</script> */',
    '  "<img src=x onerror=alert(1)>" 0x1F 42u',
    "   d:\t8b 55 ec             \tmov    -0x14(%rbp),%edx",
    "\t.loc 1 18 1 view -0",
    "($tuple ($str \"</pre><b>\") 12)",
  ];
  for (const line of lines) {
    for (const lang of ["c", "asm", "sexp", "plain"]) {
      const toks = highlightLine(line, lang);
      assert.equal(toks.map((t) => t[0]).join(""), line, `${lang}: ${line}`);
      assert.ok(toks.every((t) => typeof t[1] === "string" && /^[a-z-]*$/.test(t[1])));
    }
  }
  const c = highlightLine(lines[0], "c");
  assert.ok(c.some(([t, k]) => t === "int" && k === "tok-keyword"));
  assert.ok(c.some(([t, k]) => t.includes("<script>") && k === "tok-comment"));
  const a = highlightLine(lines[2], "asm");
  assert.ok(a.some(([t, k]) => t === "%rbp" && k === "tok-register"));
  assert.ok(a.some(([t, k]) => t === "mov" && k === "tok-keyword"));
  assert.equal(langOf("text/x-objdump"), "asm");
  assert.equal(langOf("application/json"), "plain");
});

test("disproved and open are distinct, and neither is proved", () => {
  assert.equal(badge("refuted").label, "disproved");
  assert.notEqual(badge("refuted").cls, badge("open").cls);
  assert.match(badge("open").title, /unknown/);
});

import { highlightText } from "../ui/view.js";

test("C block comments carry over lines", () => {
  const text = "/* one\n   two */ int x; /* three\nfour */";
  const lines = highlightText(text, "c");
  assert.deepEqual(lines.map((l) => l.map((t) => t[0]).join("")), text.split("\n"));
  assert.deepEqual(lines[1][0], ["   two */", "tok-comment"]);
  assert.ok(lines[1].some(([t, k]) => t === "int" && k === "tok-keyword"));
  assert.deepEqual(lines[2], [["four */", "tok-comment"]]);
});

test("include rows preserve path identity; basenames are only display labels", () => {
  const env = manifest("programs--msort--O2").include_env;
  const rows = includeRows(env);
  assert.deepEqual(rows.map((row) => row.path), env.files.map((file) => file.name));
  assert.deepEqual(rows.map((row) => row.sha256), env.files.map((file) => file.sha256));
  assert.equal(rows[0].main, true);
  const sameBasename = includeRows({ files: [
    { name: "/a/stdio.h", size: 1, sha256: "a".repeat(64) },
    { name: "/b/stdio.h", size: 1, sha256: "a".repeat(64) },
  ] });
  assert.deepEqual(sameBasename.map((row) => row.label), ["stdio.h", "stdio.h"]);
  assert.notEqual(sameBasename[0].path, sameBasename[1].path);
});

test("include rows preserve directive aliases, resolution contexts and skipped repeats", () => {
  const operand = (spelling, dest, parent) => ({ directive: "include", operand: spelling, resolved: dest, parent });
  const shared = "/a/bits/name.h";
  const alternate = "/b/bits/name.h";
  const env = { files: [shared, alternate].map((name) => ({ name, size: 4, sha256: "a".repeat(64) })),
    trace: { occurrences: [operand("<bits/name.h>", shared, null), operand('"name.h"', shared, 0),
      operand("<bits/name.h>", alternate, null), operand("<alias.h>", shared, null),
      operand("<bits/name.h>", null, null), operand("<bits/name.h>", null, null)] } };
  const rows = includeRows(env);
  assert.deepEqual(rows.map(({ label, path, kind }) => [label, path, kind]), [
    ["bits/name.h", shared, "direct"], ["name.h", shared, "indirect"],
    ["bits/name.h", alternate, "direct"], ["alias.h", shared, "direct"], ["bits/name.h", null, "direct"],
  ]);
  assert.deepEqual(rows.at(-1).events.map((event) => event.index), [4, 5]);
  assert.equal(rows.at(-1).sha256, undefined);
});

test("missing and incompatible evidence have neutral badges, not rejection", () => {
  for (const status of ["unchecked", "unavailable", "incompatible"]) {
    assert.notEqual(badge(status).cls, badge("rejected").cls);
    assert.notEqual(badge(status).cls, badge("refuted").cls);
  }
});

test("S-expression formatting wraps nested lists but keeps empty lists and literals intact", () => {
  const literal = String.raw`"a (b), \"quoted\" and \\."`;
  const raw = `(root   (nested (a b)   ()) (text ${literal}))`;
  assert.equal(prettySexp(raw, 26), `(root\n  (nested (a b) ())\n  (text\n    ${literal}\n  )\n)`);
  assert.equal(prettySexp("  ( )  "), "()");
});

test("S-expression formatting preserves line and nested block comments", () => {
  const comment = '#| one ( "\n #| inner ) |#\nlast |#';
  const raw = `; before )\n(value ; inline (\n  ${comment} (end)) ; after "`;
  assert.equal(prettySexp(raw), `; before )\n(value\n  ; inline (\n  ${comment}\n  (end)\n)\n; after "`);
});

test("incomplete or malformed input does not produce a formatted view", () => {
  for (const raw of ["", ")", "(open", '("unclosed)', '("escape\\', "(#| comment)", "(a) (b)", "FRONTEND-ERROR: failed"]) {
    assert.equal(prettySexp(raw), null, raw);
  }
});

test("real standalone Ail and Core artifacts format independently", () => {
  for (const name of ["compiles-to--straight--O0--add3", "c2c--add3_drop"]) {
    const roles = manifest(name).artifacts;
    for (const [role, head] of [["ail", "($tuple"], ["core", "($document"],
      ...(roles.target_ail ? [["target_ail", "($tuple"], ["target_core", "($document"]] : [])]) {
      const raw = text(roles[role].path);
      const formatted = prettySexp(raw);
      assert.ok(formatted.startsWith(head));
      assert.ok(formatted.split("\n").length > 100, role);
      assert.equal(prettySexp(formatted), formatted, role);
    }
  }
});

test("frontend evaluation and elaboration evidence are not interchangeable", () => {
  const manifestData = manifest("c2c--add3_drop");
  const stages = Object.fromEntries(manifestData.stages.map((stage) => [stage.output, stage]));
  const checked = { lean: manifestData.lean, bindings_checked: true };
  const proved = { status: "proved" };
  assert.equal(stageTrust(checked, stages.ail, proved), "evaluated");
  assert.equal(stageTrust(checked, stages.core, proved), "verified");
  for (const stage of [stages.core, stages.target_core]) {
    for (const status of ["unchecked", "claimed", "stale", "rejected", "refuted"]) {
      assert.equal(stageTrust(checked, stage, { status }), "unchecked");
    }
  }
  for (const stage of Object.values(stages)) {
    assert.equal(stageTrust({ ...checked, bindings_checked: false }, stage, proved), "unchecked");
  }
  assert.notEqual(stages.core.obligation, stages.target_core.obligation);
});

test("deeply nested input does not use the JavaScript call stack", () => {
  const depth = 10000;
  const formatted = prettySexp("(".repeat(depth) + "()" + ")".repeat(depth));
  assert.equal(formatted.replace(/\s+/g, "").length, 2 * depth + 2);
  assert.ok(formatted.split("\n").every((line) => line.length <= 88));
});
