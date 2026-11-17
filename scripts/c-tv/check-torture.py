#!/usr/bin/env python3
"""Invariants of the GCC torture manifest and of the stored TV report (docs/projects/c-tv.md, stage 4).

Runs in `make c-tv-check` without a GCC checkout, a compiler or the native runner: it reads only
benchmarks/gcc-torture/manifest.json and tv-report.json.gz and checks that

* the manifest pins GCC 14.3.0 (`c9cd41fb`), lists 3,852 unique C cases under compile/ and
  execute/, and every case is one of its unique, hashed inputs;
* the report names this manifest by SHA-256, pins its tools (gcc, clang and the SHA-256 of
  cerb-lean, cfront, ctv-pipeline), options, profile and native caps, and has exactly one row per
  manifest case, in manifest order;
* every row was verified against the manifest during the run (`sourceVerified`, the same
  SHA-256), unless it is `not-attempted`;
* every status is a known one and agrees with the row's facts (a `cross-validated` row has two
  validated, UB-free pairs and no blocked route; a `cross-validated-ub` one is not UB-free; a
  `no-main` one is a compile/ case; ...), only known flags occur, and the summary is the count of
  the rows (summing to the denominator).
"""
import gzip, hashlib, json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
MANIFEST = os.path.join(ROOT, "benchmarks", "gcc-torture", "manifest.json")
REPORT = os.path.join(ROOT, "benchmarks", "gcc-torture", "tv-report.json.gz")
DENOMINATOR = 3852
REVISION = "c9cd41fba9ebd288c4f101e4b99da934bcb96a11"
STATUSES = ["not-attempted", "harness-needed", "frontend-rejected", "elaborator-rejected", "no-main", "gap",
            "unknown", "explored", "cross-validated", "cross-validated-ub", "cross-validated-blocked", "refuted",
            "timeout", "tool-error"]
FIELDS = {"case", "status", "why", "routes", "sha256", "sourceVerified", "compileOnly", "targetConditional",
          "blocked", "native", "endings", "profileIncoherent", "ubReached", "coreAllowsPass", "pairs"}
ENDED = {"exit", "signal", "timeout", "stdout-limit", "build-failed"}

errors = []


def need(ok, what):
    if not ok:
        errors.append(what)


def main():
    global REPORT
    if len(sys.argv) == 3 and sys.argv[1] == "--report":
        REPORT = sys.argv[2]
    raw = open(MANIFEST, "rb").read()
    man = json.loads(raw)
    need(man["revision"] == REVISION, f"manifest revision {man['revision']}")
    cases = man["cases"]
    need(len(cases) == DENOMINATOR, f"manifest has {len(cases)} cases, not {DENOMINATOR}")
    need(len(set(cases)) == len(cases), "manifest case IDs are not unique")
    need(all(c.endswith(".c") and c.split("/")[0] in ("compile", "execute") for c in cases), "a case is not a compile/ or execute/ C file")
    paths = [i["path"] for i in man["inputs"]]
    need(len(set(paths)) == len(paths), "manifest input paths are not unique")
    sums = {i["path"]: i["sha256"] for i in man["inputs"]}
    need(all(len(h) == 64 and all(ch in "0123456789abcdef" for ch in h) for h in sums.values()), "an input hash is not a SHA-256")
    need(all(c in sums for c in cases), "a case is not a hashed input")

    rep = json.load(gzip.open(REPORT))
    need(rep["schema"] == "silmaril.c-tv.gcc-torture.v1", "report schema")
    need(rep["manifest"]["sha256"] == hashlib.sha256(raw).hexdigest(), "the report does not name this manifest's SHA-256")
    need(rep["manifest"]["revision"] == REVISION, "report manifest revision")
    need(rep["denominator"] == DENOMINATOR, "report denominator")
    for t in ("gcc", "clang"):
        need(isinstance(rep["tools"].get(t), str) and rep["tools"][t] not in ("", "unknown") and any(ch.isdigit() for ch in rep["tools"][t]), f"tool {t} not pinned by version")
    for t in ("cerb-lean", "cfront", "ctv-pipeline"):
        need(len(rep["tools"].get(t, "")) == 64, f"tool {t} not pinned by SHA-256")
    opts = rep.get("options", {})
    for k in ("preprocess", "cerberusRoute", "clangAst", "clangRoute", "pipeline", "native", "toolTimeoutSeconds", "target"):
        need(k in opts, f"option {k} not pinned")
    need(opts.get("pipeline", {}).get("profile") == "linuxX86_64", "profile not pinned")
    for k in ("timeoutSeconds", "cpuSeconds", "addressSpaceBytes", "fileSizeBytes", "stdoutBytes"):
        need(k in rep.get("native", {}), f"native cap {k} not pinned")
    need(rep["evidence"] == "compiled", "report evidence kind")

    rows = rep["cases"]
    need([r["case"] for r in rows] == cases, "report rows are not the manifest cases, in order")
    for r in rows:
        c, st = r["case"], r["status"]
        need(st in STATUSES, f"{c}: unknown status {st}")
        need(set(r) <= FIELDS, f"{c}: unknown fields {sorted(set(r) - FIELDS)}")
        if st != "not-attempted":
            need(r.get("sourceVerified") is True and r.get("sha256") == sums[c], f"{c}: source not verified against the manifest during the run")
        else:
            need("why" in r, f"{c}: not-attempted without a reason")
        need(r.get("compileOnly", False) == c.startswith("compile/") or st == "not-attempted", f"{c}: compileOnly flag")
        if "native" in r:
            need(c.startswith("execute/"), f"{c}: native run of a compile/ case")
            need(r["native"].get("ended") in ENDED, f"{c}: native ending {r['native']}")
            need(r["native"].get("ended") not in ("exit", "signal") or isinstance(r["native"].get("code"), int), f"{c}: native code")
        pairs = r.get("pairs", {})
        if st == "harness-needed":
            need("why" in r, f"{c}: harness-needed without a reason")
        if st == "no-main":
            need(c.startswith("compile/"), f"{c}: no-main outside compile/")
        if st in ("cross-validated", "cross-validated-ub", "cross-validated-blocked"):
            need(len(pairs) == 2 and all(v == "validated" for v in pairs.values()), f"{c}: {st} without two validated pairs")
        if st == "cross-validated":
            need(not r.get("blocked") and not r.get("ubReached"), f"{c}: cross-validated with a blocked route or UB")
        if st == "cross-validated-blocked":
            need(bool(r.get("blocked")), f"{c}: cross-validated-blocked without a blocked route")
        if st == "refuted":
            need("refuted" in pairs.values(), f"{c}: refuted without a refuted pair")

    summary = rep["summary"]
    counts = {s: sum(1 for r in rows if r["status"] == s) for s in STATUSES}
    need(all(summary.get(s, 0) == counts[s] for s in STATUSES), "summary is not the count of the rows")
    need(sum(counts.values()) == DENOMINATOR, "statuses do not sum to the denominator")
    for part in ("compile/", "execute/"):
        need(all(summary[part].get(s, 0) == sum(1 for r in rows if r["status"] == s and r["case"].startswith(part)) for s in STATUSES),
             f"summary {part} is not the count of the rows")

    if errors:
        for e in errors[:50]:
            print("FAIL", e)
        print(f"{len(errors)} invariant(s) fail")
        sys.exit(1)
    print(f"torture manifest and report: {DENOMINATOR} cases, statuses sum to the denominator, every attempted source "
          "verified against the manifest, tools/options/profile/caps pinned (invariants only: no case is re-run)")


main()
