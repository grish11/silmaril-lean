#!/usr/bin/env python3
"""The compiler explorer's database and read-only API.

    python3 -I tools/compiler-explorer/cexplorer.py ingest DB MANIFEST...   # problems (with their artifacts)
    python3 -I tools/compiler-explorer/cexplorer.py evidence DB EVIDENCE... # export.lean outputs
    python3 -I tools/compiler-explorer/cexplorer.py status DB [PROBLEM]     # a text report
    python3 -I tools/compiler-explorer/cexplorer.py serve DB [--host 127.0.0.1] [--port 8765]

docs/projects/compiler-explorer.md describes the model. In short:

* **Artifacts** are immutable and content-addressed (SHA-256). Ingesting a manifest reads every
  file it names from the repository, checks its SHA-256 and size, and stores the bytes. A second
  artifact with the same address must have the same bytes.
* A **problem version** is one manifest: its artifacts by role, the derivation (compiler,
  version, image, command), the execution models, ABI, mapping relation and comorphism, the
  fragments, edges and obligations. Its *context hash* covers all of these. Re-ingesting a
  changed manifest makes a new version; evidence never moves between versions.
* **Evidence** for an obligation comes only from tools/compiler-explorer/export.lean output for
  the exact manifest (by SHA-256), with the same statement and declaration. Anything else is
  rejected and logged. Tests (running compiled code) are stored as tests, never as evidence for
  an obligation.
* Every Lean **statement** is the template of its obligation kind applied to the manifest's Lean
  names (`TEMPLATES`): a manifest cannot attach a convenient statement (`True`) to an
  obligation.

The server answers GET requests only, opens the database read-only, and has no endpoint that
compiles or runs anything.
"""

from __future__ import annotations

import hashlib
import http.server
import json
import pathlib
import sqlite3
import sys
import tomllib
import urllib.parse

ROOT = pathlib.Path(__file__).resolve().parents[2]
UI = pathlib.Path(__file__).resolve().parent / "ui"

PROBLEM_SCHEMA = "silmaril.compiler-explorer.problem/1"
EVIDENCE_SCHEMA = "silmaril.compiler-explorer.evidence/1"
DIRECTIONS = ("compiled", "decompiled", "imported")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPORT_STATUSES = {"kernel", "open", "missing", "not_theorem", "mismatch", "bad_axioms", "elab_error"}
MAX_TEXT = 1 << 20  # the largest artifact the API returns as text

# ------------------------------------------------------------------------------------------------
# Statement templates

K0 = "∀ k0 : List Silmaril.Cerberus.Core.Dynamics.Frame,"

# Per family, per obligation kind: the Lean statement, from the manifest's `lean.vars` and the
# obligation's point (`k`) and line. `None` for kinds the family does not state.
TEMPLATES = {
    "c-function-x86": {
        "translation": lambda v, k, line: f"{K0} ({v['fn']}.compilation {v['isa']} k0).Valid",
        "mapping": lambda v, k, line: f"{K0} ({v['fn']}.mapping {v['isa']} k0).Valid",
        "edge": lambda v, k, line: f"{K0} ({v['fn']}.mapping {v['isa']} k0).EdgeValid {k}",
        "refinement": lambda v, k, line: (
            f"{K0} ({v['fn']}.mapping {v['isa']} k0).RefinesComorphism {v['comorphism']} "
            f"{v['fn']}.scope (fun _ => True)"),
        "abi": lambda v, k, line: (
            f"Silmaril.Project.Shapes.SysV.Enterable {v['isa']} {v['fn']}.placement "
            f"{v['fn']}.sig {v['fn']}.frame"),
        "point": lambda v, k, line: f"Silmaril.Project.Shapes.CompilesTo.PointOf {v['fn']} {k} {line}",
        "elaboration": lambda v, k, line: (
            f"Silmaril.Project.Shapes.C.ElaboratesTo {v['ail']} \"{v['cname']}\" {v['cfn']}"),
        "nonvacuity_canonical": lambda v, k, line: (
            f"Silmaril.Project.Shapes.CompilesTo.CompilesToCanonical {v['isa']} {v['fn']}.placement "
            f"{v['fn']}.frame {v['cfn']}"),
        "nonvacuity_universal": lambda v, k, line: f"{v['cfn']}.meaning.Inhabited",
        "artifact": lambda v, k, line: v["code_prop"],
    },
}
KINDS = ("translation", "mapping", "edge", "refinement", "abi", "point", "elaboration",
         "nonvacuity_canonical", "nonvacuity_universal", "artifact")
FAMILY_VARS = {"c-function-x86": ("fn", "cfn", "ail", "cname", "isa", "comorphism", "code_prop")}


class Rejected(Exception):
    """A manifest, an artifact or a claim the database refuses."""


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(obj) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def fragment_id(artifact_sha: str, space: str, ranges: list[list[int]]) -> str:
    return sha256(f"{artifact_sha}:{space}:{json.dumps(sorted(ranges))}".encode())[:20]


def statement_for(family: str, vars_: dict, kind: str, point, line):
    t = TEMPLATES.get(family, {}).get(kind)
    return None if t is None else t(vars_, point, line)


# ------------------------------------------------------------------------------------------------
# Schema and migrations

MIGRATIONS = [
    # 1: the initial schema
    """
    CREATE TABLE artifacts (
      sha256 TEXT PRIMARY KEY CHECK (length(sha256) = 64),
      size INTEGER NOT NULL,
      content BLOB NOT NULL
    );
    CREATE TABLE problems (
      id TEXT PRIMARY KEY,
      current_version INTEGER NOT NULL
    );
    CREATE TABLE problem_versions (
      id INTEGER PRIMARY KEY,
      problem_id TEXT NOT NULL,
      manifest_sha256 TEXT NOT NULL UNIQUE,
      context_hash TEXT NOT NULL,
      title TEXT NOT NULL,
      direction TEXT NOT NULL CHECK (direction IN ('compiled', 'decompiled', 'imported')),
      family TEXT,
      derivation TEXT,
      context TEXT NOT NULL,
      lean TEXT NOT NULL,
      view TEXT NOT NULL,
      extra TEXT NOT NULL
    );
    CREATE TABLE version_artifacts (
      version_id INTEGER NOT NULL REFERENCES problem_versions(id),
      role TEXT NOT NULL,
      sha256 TEXT NOT NULL REFERENCES artifacts(sha256),
      path TEXT NOT NULL,
      media TEXT NOT NULL,
      PRIMARY KEY (version_id, role)
    );
    CREATE TABLE fragments (
      version_id INTEGER NOT NULL REFERENCES problem_versions(id),
      id TEXT NOT NULL,
      role TEXT NOT NULL CHECK (role IN ('source', 'target')),
      space TEXT NOT NULL,
      ranges TEXT NOT NULL,
      label TEXT NOT NULL,
      PRIMARY KEY (version_id, id)
    );
    CREATE TABLE edges (
      version_id INTEGER NOT NULL REFERENCES problem_versions(id),
      id TEXT NOT NULL,
      kind TEXT NOT NULL CHECK (kind IN ('navigation', 'semantic')),
      origin TEXT,
      function TEXT,
      point INTEGER,
      point_kind TEXT,
      note TEXT,
      PRIMARY KEY (version_id, id)
    );
    CREATE TABLE edge_ends (
      version_id INTEGER NOT NULL,
      edge_id TEXT NOT NULL,
      side TEXT NOT NULL CHECK (side IN ('source', 'target')),
      fragment_id TEXT NOT NULL,
      PRIMARY KEY (version_id, edge_id, side, fragment_id),
      FOREIGN KEY (version_id, edge_id) REFERENCES edges(version_id, id),
      FOREIGN KEY (version_id, fragment_id) REFERENCES fragments(version_id, id)
    );
    CREATE TABLE obligations (
      version_id INTEGER NOT NULL REFERENCES problem_versions(id),
      id TEXT NOT NULL,
      kind TEXT NOT NULL,
      statement TEXT,
      decl TEXT,
      edge_id TEXT,
      unsupported TEXT,
      PRIMARY KEY (version_id, id),
      CHECK ((statement IS NULL) = (unsupported IS NOT NULL))
    );
    CREATE TABLE evidence (
      id INTEGER PRIMARY KEY,
      version_id INTEGER NOT NULL REFERENCES problem_versions(id),
      obligation_id TEXT NOT NULL,
      kind TEXT NOT NULL CHECK (kind IN ('lean-export')),
      status TEXT NOT NULL,
      manifest_sha256 TEXT NOT NULL,
      context_hash TEXT NOT NULL,
      statement TEXT NOT NULL,
      decl TEXT,
      axioms TEXT,
      lean_version TEXT NOT NULL,
      git_commit TEXT NOT NULL,
      evidence_sha256 TEXT NOT NULL,
      detail TEXT,
      FOREIGN KEY (version_id, obligation_id) REFERENCES obligations(version_id, id)
    );
    CREATE TABLE tests (
      version_id INTEGER NOT NULL REFERENCES problem_versions(id),
      id TEXT NOT NULL,
      kind TEXT NOT NULL,
      about_sha256 TEXT NOT NULL,
      status TEXT NOT NULL CHECK (status IN ('passed', 'failed', 'stale')),
      record TEXT NOT NULL,
      PRIMARY KEY (version_id, id)
    );
    CREATE TABLE rejections (
      id INTEGER PRIMARY KEY,
      what TEXT NOT NULL,
      reason TEXT NOT NULL
    );
    """,
]


def connect(path: str, readonly: bool = False) -> sqlite3.Connection:
    if readonly:
        uri = pathlib.Path(path).resolve().as_uri() + "?mode=ro"
        db = sqlite3.connect(uri, uri=True, check_same_thread=False)
    else:
        db = sqlite3.connect(path)
        migrate(db)
    db.row_factory = sqlite3.Row
    db.execute("PRAGMA foreign_keys = ON")
    return db


def migrate(db: sqlite3.Connection) -> None:
    db.execute("CREATE TABLE IF NOT EXISTS schema_migrations (version INTEGER PRIMARY KEY)")
    done = {r[0] for r in db.execute("SELECT version FROM schema_migrations")}
    for i, sql in enumerate(MIGRATIONS, start=1):
        if i not in done:
            with db:
                db.executescript("BEGIN;" + sql + f"INSERT INTO schema_migrations VALUES ({i}); COMMIT;")


def reject(db: sqlite3.Connection, what: str, reason: str) -> Rejected:
    with db:
        db.execute("INSERT INTO rejections (what, reason) VALUES (?, ?)", (what, reason))
    return Rejected(f"{what}: {reason}")


# ------------------------------------------------------------------------------------------------
# Ingesting a manifest


def read_artifact(root: pathlib.Path, ref: dict) -> bytes:
    rel = pathlib.PurePosixPath(ref["path"])
    if rel.is_absolute() or ".." in rel.parts:
        raise ValueError(f"artifact path must be relative and inside the repository: {rel}")
    data = (root / rel).read_bytes()
    if sha256(data) != ref["sha256"] or len(data) != ref["size"]:
        raise ValueError(f"{rel}: the file's bytes are not the manifest's "
                         f"(sha256 {sha256(data)}, size {len(data)}; manifest {ref['sha256']}, {ref['size']})")
    return data


def store_artifact(db: sqlite3.Connection, data: bytes) -> str:
    h = sha256(data)
    row = db.execute("SELECT content FROM artifacts WHERE sha256 = ?", (h,)).fetchone()
    if row is None:
        db.execute("INSERT INTO artifacts (sha256, size, content) VALUES (?, ?, ?)", (h, len(data), data))
    elif bytes(row[0]) != data:  # cannot happen without a SHA-256 collision or a corrupted row
        raise ValueError(f"artifact {h}: stored bytes differ")
    return h


def registry_sha(root: pathlib.Path, name: str) -> str | None:
    reg = tomllib.loads((root / "silmaril" / "artifacts.toml").read_text())
    for a in reg.get("artifact", []):
        if a.get("name") == name:
            return a.get("sha256")
    return None


def check_manifest(root: pathlib.Path, m: dict, blobs: dict[str, bytes]) -> None:
    """Every structural check that does not need the database. Raises ValueError."""
    if m.get("schema") != PROBLEM_SCHEMA:
        raise ValueError(f"unexpected schema {m.get('schema')!r}")
    if m.get("direction") not in DIRECTIONS:
        raise ValueError(f"direction must be one of {DIRECTIONS}")
    arts = m["artifacts"]
    for role in ("source", "target"):
        if role not in arts:
            raise ValueError(f"no {role} artifact")
    shas = {role: ref["sha256"] for role, ref in arts.items()}
    # the derivation: a compiled target names its compiler and a receipt about these bytes
    d = m.get("derivation")
    if m["direction"] in ("compiled", "decompiled"):
        if not d or not all(d.get(k) for k in ("compiler", "version", "image", "command")):
            raise ValueError("a compiled or decompiled problem records its tool, version, image and command")
        rec = json.loads(blobs[d["receipt"]])
        about = {rec.get("source", {}).get("sha256")}
        made = {rec.get(k, {}).get("sha256") for k in ("object", "assembly", "output")} - {None}
        if shas["source"] not in about or shas["target"] not in made:
            raise ValueError("the receipt is about other bytes than the source and target artifacts")
        if rec.get("image") != d["image"]:
            raise ValueError("the receipt's image is not the derivation's")
    # fragments: content addresses
    frags = {}
    for f in m["fragments"]:
        role = f["artifact"]
        if role not in ("source", "target"):
            raise ValueError(f"fragment {f['id']}: artifact must be source or target")
        if fragment_id(shas[role], f["space"], f["ranges"]) != f["id"]:
            raise ValueError(f"fragment {f['id']}: its id is not the address of its ranges in {role}")
        for lo, hi in f["ranges"]:
            if not 0 <= lo <= hi:
                raise ValueError(f"fragment {f['id']}: bad range")
            if f["space"] == "bytes" and hi > len(blobs[role]):
                raise ValueError(f"fragment {f['id']}: range outside the artifact")
        frags[f["id"]] = f
    # edges
    edge_ids = set()
    for e in m["edges"]:
        if e["kind"] not in ("navigation", "semantic"):
            raise ValueError(f"edge {e['id']}: unknown kind")
        if e["id"] in edge_ids:
            raise ValueError(f"edge {e['id']}: duplicate")
        edge_ids.add(e["id"])
        if e["kind"] == "semantic" and not isinstance(e.get("point"), int):
            raise ValueError(f"edge {e['id']}: a semantic edge names its program point")
        for side in ("source", "target"):
            for fid in e[side]:
                if fid not in frags or frags[fid]["artifact"] != side:
                    raise ValueError(f"edge {e['id']}: {side} fragment {fid} is not a {side} fragment")
    edges = {e["id"]: e for e in m["edges"]}
    # obligations: statements are the family's templates
    lean = m.get("lean", {})
    family = lean.get("family")
    vars_ = lean.get("vars", {})
    if family is not None:
        if family not in TEMPLATES:
            raise ValueError(f"unknown family {family!r}")
        missing = [k for k in FAMILY_VARS[family] if not vars_.get(k)]
        if missing:
            raise ValueError(f"family {family} needs the Lean names {missing}")
    ids = set()
    for o in m["obligations"]:
        if o["id"] in ids:
            raise ValueError(f"obligation {o['id']}: duplicate")
        ids.add(o["id"])
        if o["kind"] not in KINDS:
            raise ValueError(f"obligation {o['id']}: unknown kind {o['kind']!r}")
        if o.get("statement") is None:
            if not o.get("unsupported"):
                raise ValueError(f"obligation {o['id']}: no statement and no reason")
            if o.get("decl"):
                raise ValueError(f"obligation {o['id']}: a declaration without a statement")
            continue
        if family is None:
            raise ValueError(f"obligation {o['id']}: a statement needs a Lean family")
        e = edges.get(o.get("edge")) if o.get("edge") else None
        if o["kind"] in ("edge", "point") and (e is None or e["kind"] != "semantic"):
            raise ValueError(f"obligation {o['id']}: an {o['kind']} obligation is about a semantic edge")
        expected = statement_for(family, vars_, o["kind"], e and e["point"], e and e.get("line"))
        if expected is None or o["statement"] != expected:
            raise ValueError(f"obligation {o['id']}: the statement is not the {o['kind']} statement "
                             f"of this problem (expected {expected!r})")
    # registered artifacts: the Lean values read these bytes
    for role, name in lean.get("registry", {}).items():
        if registry_sha(root, name) != shas.get(role):
            raise ValueError(f"the registry's {name} is not the {role} artifact")


def ingest_manifest(db: sqlite3.Connection, path: pathlib.Path, root: pathlib.Path = ROOT) -> int:
    raw = path.read_bytes()
    msha = sha256(raw)
    try:
        m = json.loads(raw)
        blobs = {role: read_artifact(root, ref) for role, ref in m["artifacts"].items()}
        check_manifest(root, m, blobs)
    except (ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        raise reject(db, f"manifest {path}", str(exc)) from None
    row = db.execute("SELECT id FROM problem_versions WHERE manifest_sha256 = ?", (msha,)).fetchone()
    if row is not None:
        return row[0]
    lean = m.get("lean", {})
    context = {"artifacts": {r: a["sha256"] for r, a in sorted(m["artifacts"].items())},
               "derivation": m.get("derivation"), "context": m["context"],
               "lean": {"family": lean.get("family"), "vars": lean.get("vars", {}),
                        "modules": lean.get("modules", [])}}
    ctx_hash = sha256(canonical(context))
    extra = {k: m[k] for k in ("navigation_stats", "tests") if k in m}
    with db:
        for data in blobs.values():
            store_artifact(db, data)
        cur = db.execute(
            "INSERT INTO problem_versions (problem_id, manifest_sha256, context_hash, title, direction,"
            " family, derivation, context, lean, view, extra) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
            (m["id"], msha, ctx_hash, m["title"], m["direction"], lean.get("family"),
             json.dumps(m.get("derivation")), json.dumps(m["context"]), json.dumps(lean),
             json.dumps(m["view"]), json.dumps(extra)))
        vid = cur.lastrowid
        for role, ref in m["artifacts"].items():
            db.execute("INSERT INTO version_artifacts VALUES (?,?,?,?,?)",
                       (vid, role, ref["sha256"], ref["path"], ref["media"]))
        for f in m["fragments"]:
            db.execute("INSERT INTO fragments VALUES (?,?,?,?,?,?)",
                       (vid, f["id"], f["artifact"], f["space"], json.dumps(f["ranges"]), f["label"]))
        for e in m["edges"]:
            db.execute("INSERT INTO edges VALUES (?,?,?,?,?,?,?,?)",
                       (vid, e["id"], e["kind"], e.get("origin"), e.get("function"), e.get("point"),
                        e.get("point_kind"), e.get("note")))
            for side in ("source", "target"):
                for fid in e[side]:
                    db.execute("INSERT INTO edge_ends VALUES (?,?,?,?)", (vid, e["id"], side, fid))
        for o in m["obligations"]:
            db.execute("INSERT INTO obligations VALUES (?,?,?,?,?,?,?)",
                       (vid, o["id"], o["kind"], o.get("statement"), o.get("decl"), o.get("edge"),
                        o.get("unsupported")))
        for t in m.get("tests", []):
            rec_bytes = blobs[t["artifact"]]
            rec = json.loads(rec_bytes)
            about = m["artifacts"][t["about"]]["sha256"]
            if rec.get("assembly_sha256") != about:
                status = "stale"
            elif rec.get("exit") == 0 and rec.get("stdout") == t.get("expected_stdout"):
                status = "passed"
            else:
                status = "failed"
            rec = dict(rec, expected_stdout=t.get("expected_stdout"))
            db.execute("INSERT INTO tests VALUES (?,?,?,?,?,?)",
                       (vid, t["id"], t["kind"], about, status, json.dumps(rec)))
        db.execute("INSERT INTO problems (id, current_version) VALUES (?, ?) "
                   "ON CONFLICT(id) DO UPDATE SET current_version = excluded.current_version",
                   (m["id"], vid))
    return vid


# ------------------------------------------------------------------------------------------------
# Ingesting evidence


def ingest_evidence(db: sqlite3.Connection, path: pathlib.Path) -> int:
    raw = path.read_bytes()
    esha = sha256(raw)
    what = f"evidence {path}"
    try:
        ev = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise reject(db, what, f"not JSON: {exc}") from None
    if ev.get("schema") != EVIDENCE_SCHEMA:
        raise reject(db, what, f"unexpected schema {ev.get('schema')!r}")
    ver = db.execute("SELECT * FROM problem_versions WHERE manifest_sha256 = ?",
                     (ev.get("manifest_sha256"),)).fetchone()
    if ver is None:
        raise reject(db, what, "it is about a manifest the database does not hold (stale or foreign)")
    if ver["problem_id"] != ev.get("problem"):
        raise reject(db, what, "its problem is not the manifest's")
    lean = json.loads(ver["lean"])
    if sorted(ev.get("modules", [])) != sorted(lean.get("modules", [])):
        raise reject(db, what, "it was computed from other Lean modules than the manifest names")
    if not ev.get("lean_version") or not ev.get("git_commit"):
        raise reject(db, what, "it does not record the Lean version and the commit it was computed at")
    obls = {r["id"]: r for r in db.execute("SELECT * FROM obligations WHERE version_id = ?", (ver["id"],))}
    rows = []
    for r in ev.get("obligations", []):
        o = obls.get(r.get("id"))
        if o is None:
            raise reject(db, what, f"obligation {r.get('id')!r} is not in the manifest")
        if o["statement"] is None or r.get("statement") != o["statement"] or r.get("decl") != o["decl"]:
            raise reject(db, what, f"obligation {o['id']}: statement or declaration differs from the manifest")
        status = r.get("status")
        if status not in EXPORT_STATUSES:
            raise reject(db, what, f"obligation {o['id']}: unknown status {status!r}")
        axioms = r.get("axioms") or []
        if status == "kernel" and (o["decl"] is None or not set(axioms) <= ALLOWED_AXIOMS):
            raise reject(db, what, f"obligation {o['id']}: a kernel status needs a declaration and the standard axioms")
        if status == "open" and o["decl"] is not None:
            raise reject(db, what, f"obligation {o['id']}: open, yet the manifest names a declaration")
        rows.append((ver["id"], o["id"], "lean-export", status, ver["manifest_sha256"], ver["context_hash"],
                     o["statement"], o["decl"], json.dumps(axioms), ev["lean_version"], ev["git_commit"],
                     esha, r.get("detail")))
    with db:
        db.execute("DELETE FROM evidence WHERE version_id = ? AND evidence_sha256 = ?", (ver["id"], esha))
        db.executemany("INSERT INTO evidence (version_id, obligation_id, kind, status, manifest_sha256,"
                       " context_hash, statement, decl, axioms, lean_version, git_commit, evidence_sha256,"
                       " detail) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?)", rows)
    return len(rows)


# ------------------------------------------------------------------------------------------------
# Queries: statuses are computed here, from the database, for the current version only

STATUS_TEXT = {
    "proved": "checked by Lean's kernel",
    "open": "stated in Lean, not proved",
    "unchecked": "a proof is claimed but no checked evidence is recorded",
    "rejected": "the claimed proof was checked and does not prove the statement",
    "stale": "proved for another version of this problem only",
    "unsupported": "not stated: no model covers it",
}


def obligation_status(db, ver, o) -> dict:
    if o["unsupported"]:
        return {"status": "unsupported", "reason": o["unsupported"]}
    evs = db.execute("SELECT * FROM evidence WHERE version_id = ? AND obligation_id = ? ORDER BY id DESC",
                     (ver["id"], o["id"])).fetchall()
    evs = [e for e in evs if e["context_hash"] == ver["context_hash"]
           and e["manifest_sha256"] == ver["manifest_sha256"] and e["statement"] == o["statement"]
           and e["decl"] == o["decl"]]
    if evs:
        e = evs[0]
        if e["status"] == "kernel":
            status = "proved"
        elif e["status"] == "open":
            status = "open"
        else:
            status = "rejected"
        return {"status": status, "evidence": {
            "kind": e["kind"], "export_status": e["status"], "decl": e["decl"],
            "axioms": json.loads(e["axioms"] or "[]"), "lean_version": e["lean_version"],
            "git_commit": e["git_commit"], "evidence_sha256": e["evidence_sha256"],
            "detail": e["detail"]}}
    older = db.execute(
        "SELECT pv.manifest_sha256 FROM evidence ev JOIN problem_versions pv ON pv.id = ev.version_id "
        "WHERE pv.problem_id = ? AND ev.obligation_id = ? AND ev.status = 'kernel' AND pv.id != ?",
        (ver["problem_id"], o["id"], ver["id"])).fetchone()
    if older is not None and o["decl"] is not None:
        return {"status": "stale", "older_manifest": older[0]}
    return {"status": "open" if o["decl"] is None else "unchecked"}


def artifact_text(db, sha: str) -> str | None:
    row = db.execute("SELECT content, size FROM artifacts WHERE sha256 = ?", (sha,)).fetchone()
    if row is None or row["size"] > MAX_TEXT:
        return None
    try:
        return bytes(row["content"]).decode("utf-8")
    except UnicodeDecodeError:
        return None


def problem_list(db) -> list[dict]:
    out = []
    for p in db.execute("SELECT p.id, pv.* FROM problems p JOIN problem_versions pv ON pv.id = p.current_version "
                        "ORDER BY p.id"):
        obls = db.execute("SELECT * FROM obligations WHERE version_id = ?", (p["id"],)).fetchall()
        summary = {}
        for o in obls:
            if o["kind"] in ("translation", "mapping", "refinement", "abi"):
                summary[o["kind"]] = obligation_status(db, p, o)["status"]
        out.append({"id": p["problem_id"], "title": p["title"], "direction": p["direction"],
                    "derivation": json.loads(p["derivation"]), "summary": summary})
    return out


def problem_view(db, pid: str) -> dict | None:
    ver = db.execute("SELECT pv.* FROM problems p JOIN problem_versions pv ON pv.id = p.current_version "
                     "WHERE p.id = ?", (pid,)).fetchone()
    if ver is None:
        return None
    arts = {r["role"]: {"sha256": r["sha256"], "path": r["path"], "media": r["media"],
                        "size": db.execute("SELECT size FROM artifacts WHERE sha256 = ?", (r["sha256"],)).fetchone()[0]}
            for r in db.execute("SELECT * FROM version_artifacts WHERE version_id = ?", (ver["id"],))}
    view = json.loads(ver["view"])
    texts = {side: artifact_text(db, arts[view[side]]["sha256"]) for side in ("source", "target")}
    frags = {r["id"]: {"id": r["id"], "role": r["role"], "space": r["space"],
                       "ranges": json.loads(r["ranges"]), "label": r["label"]}
             for r in db.execute("SELECT * FROM fragments WHERE version_id = ?", (ver["id"],))}
    edges = []
    for e in db.execute("SELECT * FROM edges WHERE version_id = ? ORDER BY rowid", (ver["id"],)):
        ends = db.execute("SELECT side, fragment_id FROM edge_ends WHERE version_id = ? AND edge_id = ?",
                          (ver["id"], e["id"])).fetchall()
        edges.append({"id": e["id"], "kind": e["kind"], "origin": e["origin"], "function": e["function"],
                      "point": e["point"], "point_kind": e["point_kind"], "note": e["note"],
                      "source": [x[1] for x in ends if x[0] == "source"],
                      "target": [x[1] for x in ends if x[0] == "target"]})
    obligations = []
    for o in db.execute("SELECT * FROM obligations WHERE version_id = ? ORDER BY rowid", (ver["id"],)):
        st = obligation_status(db, ver, o)
        obligations.append({"id": o["id"], "kind": o["kind"], "statement": o["statement"],
                            "decl": o["decl"], "edge": o["edge_id"], **st,
                            "status_text": STATUS_TEXT[st["status"]]})
    tests = [{"id": t["id"], "kind": t["kind"], "about_sha256": t["about_sha256"], "status": t["status"],
              "record": json.loads(t["record"])}
             for t in db.execute("SELECT * FROM tests WHERE version_id = ?", (ver["id"],))]
    versions = [{"manifest_sha256": r["manifest_sha256"], "context_hash": r["context_hash"],
                 "current": r["id"] == ver["id"]}
                for r in db.execute("SELECT * FROM problem_versions WHERE problem_id = ? ORDER BY id", (pid,))]
    by_kind = {o["kind"]: o for o in obligations if o["kind"] not in ("edge", "point")}
    edge_obls = [o for o in obligations if o["kind"] == "edge"]
    return {
        "id": pid, "title": ver["title"], "direction": ver["direction"], "family": ver["family"],
        "manifest_sha256": ver["manifest_sha256"], "context_hash": ver["context_hash"],
        "derivation": json.loads(ver["derivation"]), "context": json.loads(ver["context"]),
        "lean": json.loads(ver["lean"]), "artifacts": arts, "view": view, "texts": texts,
        "fragments": frags, "edges": edges, "obligations": obligations, "tests": tests,
        "versions": versions, "extra": json.loads(ver["extra"]),
        "questions": {
            "translation": by_kind.get("translation"),
            "abi": by_kind.get("abi"),
            "mapping": by_kind.get("mapping"),
            "refinement": by_kind.get("refinement"),
            "edges": {"proved": sum(o["status"] == "proved" for o in edge_obls), "listed": len(edge_obls),
                      "note": ("individually proved edges do not prove the mapping: coverage of the "
                               "points nobody listed is part of the mapping obligation only")},
        },
    }


# ------------------------------------------------------------------------------------------------
# The read-only server


class Handler(http.server.BaseHTTPRequestHandler):
    db_path = ""
    server_version = "silmaril-compiler-explorer"
    STATIC = {"/": ("index.html", "text/html; charset=utf-8"),
              "/app.js": ("app.js", "text/javascript; charset=utf-8"),
              "/style.css": ("style.css", "text/css; charset=utf-8"),
              "/view.js": ("view.js", "text/javascript; charset=utf-8")}

    def send(self, code: int, body: bytes, ctype: str) -> None:
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy",
                         "default-src 'self'; script-src 'self'; style-src 'self'; object-src 'none'; "
                         "base-uri 'none'; frame-ancestors 'none'")
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def json(self, code: int, obj) -> None:
        self.send(code, json.dumps(obj, ensure_ascii=False).encode(), "application/json; charset=utf-8")

    def do_GET(self) -> None:  # noqa: N802
        path = urllib.parse.urlsplit(self.path).path
        if path in self.STATIC:
            name, ctype = self.STATIC[path]
            self.send(200, (UI / name).read_bytes(), ctype)
            return
        db = connect(self.db_path, readonly=True)
        try:
            if path == "/api/problems":
                self.json(200, problem_list(db))
            elif path.startswith("/api/problems/"):
                pid = urllib.parse.unquote(path[len("/api/problems/"):])
                v = problem_view(db, pid)
                self.json(200 if v else 404, v or {"error": "no such problem"})
            else:
                self.json(404, {"error": "not found"})
        finally:
            db.close()

    do_HEAD = do_GET

    def refuse(self) -> None:
        self.json(405, {"error": "read-only: this server neither compiles nor stores anything"})

    do_POST = do_PUT = do_DELETE = do_PATCH = refuse

    def log_message(self, fmt, *args) -> None:
        sys.stderr.write("%s %s\n" % (self.address_string(), fmt % args))


def serve(db_path: str, host: str, port: int) -> None:
    connect(db_path, readonly=True).close()
    Handler.db_path = db_path
    srv = http.server.ThreadingHTTPServer((host, port), Handler)
    print(f"serving {db_path} on http://{host}:{port}/", flush=True)
    srv.serve_forever()


def status_report(db, pid: str | None) -> str:
    lines = []
    for p in problem_list(db):
        if pid and p["id"] != pid:
            continue
        v = problem_view(db, p["id"])
        lines.append(f"{p['id']}  [{v['direction']}]  {v['title']}")
        for o in v["obligations"]:
            lines.append(f"  {o['id']:<22} {o['status']:<12} {o.get('decl') or ''}")
        for t in v["tests"]:
            lines.append(f"  test {t['id']:<17} {t['status']}")
    return "\n".join(lines)


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    cmd, db_path, rest = argv[1], argv[2], argv[3:]
    if cmd == "serve":
        host, port = "127.0.0.1", 8765
        if "--host" in rest:
            host = rest[rest.index("--host") + 1]
        if "--port" in rest:
            port = int(rest[rest.index("--port") + 1])
        serve(db_path, host, port)
        return 0
    db = connect(db_path)
    status = 0
    if cmd in ("ingest", "evidence"):
        for f in rest:
            try:
                if cmd == "ingest":
                    print(f"{f}: version {ingest_manifest(db, pathlib.Path(f))}")
                else:
                    print(f"{f}: {ingest_evidence(db, pathlib.Path(f))} obligations")
            except Rejected as exc:
                print(f"rejected: {exc}", file=sys.stderr)
                status = 1
    elif cmd == "status":
        print(status_report(db, rest[0] if rest else None))
    else:
        print(__doc__, file=sys.stderr)
        return 2
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
