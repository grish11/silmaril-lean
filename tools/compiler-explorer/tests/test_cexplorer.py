#!/usr/bin/env python3
"""Tests of the compiler explorer's database and API (python3 -I, standard library only).

The evidence files here are written by the tests in the exporter's format, to test what the
database accepts and how it computes statuses; tools/compiler-explorer/check.sh runs the real
exporter on the real Lean build.
"""

from __future__ import annotations

import copy
import http.client
import importlib.util
import json
import pathlib
import shutil
import sqlite3
import tempfile
import threading
import unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("cexplorer", HERE.parent / "cexplorer.py")
cx = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cx)

ROOT = cx.ROOT
MANIFESTS = ROOT / "examples" / "compiler-explorer" / "manifests"
STRAIGHT_O0 = MANIFESTS / "compiles-to--straight--O0--add3.json"
BRANCH_O2 = MANIFESTS / "compiles-to--branch--O2--max2.json"
MSORT_O2 = MANIFESTS / "programs--msort--O2.json"
LOOP_O0 = MANIFESTS / "compiles-to--loop--O0--sum_to.json"


def evidence_for(manifest_path: pathlib.Path, status_of=lambda o: "kernel", edit=None) -> dict:
    """Evidence in the exporter's format: every obligation with a declaration gets `status_of`."""
    m = json.loads(manifest_path.read_bytes())
    obls = []
    for o in m["obligations"]:
        if o.get("statement") is None:
            continue
        if o.get("decl") is None:
            obls.append({"id": o["id"], "statement": o["statement"], "decl": None, "status": "open"})
        else:
            obls.append({"id": o["id"], "statement": o["statement"], "decl": o["decl"],
                         "status": status_of(o), "axioms": ["propext", "Classical.choice", "Quot.sound"],
                         "type": o["statement"]})
    ev = {"schema": cx.EVIDENCE_SCHEMA, "problem": m["id"],
          "manifest_sha256": cx.sha256(manifest_path.read_bytes()),
          "lean_version": "4.37.0-test", "git_commit": "0" * 40,
          "modules": m["lean"]["modules"], "obligations": obls}
    if edit:
        edit(ev)
    return ev


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = pathlib.Path(tempfile.mkdtemp())
        self.db = cx.connect(str(self.tmp / "t.sqlite"))

    def tearDown(self):
        self.db.close()
        shutil.rmtree(self.tmp)

    def write(self, name: str, obj) -> pathlib.Path:
        p = self.tmp / name
        p.write_text(json.dumps(obj, ensure_ascii=False))
        return p

    def trusted(self, path):
        """Record an evidence file as if this tool had run the exporter (`verify`)."""
        return cx.ingest_evidence(self.db, path, origin="exporter-run")

    def statuses(self, pid: str) -> dict:
        return {o["id"]: o["status"] for o in cx.problem_view(self.db, pid)["obligations"]}

    def rejections(self) -> list[str]:
        return [r["reason"] for r in self.db.execute("SELECT reason FROM rejections")]


class Ingest(Base):
    def test_proved_only_with_evidence(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        before = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(before["translation"], "unchecked")  # a proof is named, nothing checked
        self.assertEqual(before["nonvacuity/universal"], "open")
        self.trusted(self.write("ev.json", evidence_for(STRAIGHT_O0)))
        after = self.statuses("compiles-to/straight/O0/add3")
        for k in ("translation", "mapping", "refinement", "abi", "edge/0", "edge/4", "point/2", "artifact"):
            self.assertEqual(after[k], "proved", k)
        self.assertEqual(after["nonvacuity/universal"], "open")

    def test_open_mapping_with_proved_refinement(self):
        cx.ingest_manifest(self.db, BRANCH_O2)
        self.trusted(self.write("ev.json", evidence_for(BRANCH_O2)))
        st = self.statuses("compiles-to/branch/O2/max2")
        for k in ("refinement", "abi", "nonvacuity"):
            self.assertEqual(st[k], "proved", k)
        for k in ("edge/0", "mapping", "translation"):
            self.assertEqual(st[k], "open", k)

    def test_exporter_mismatch_is_rejected_status(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0, lambda o: "mismatch" if o["id"] == "edge/1" else "kernel")
        self.trusted(self.write("ev.json", ev))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["edge/1"], "rejected")
        self.assertEqual(st["edge/0"], "proved")

    def test_unsupported_and_tests_never_prove(self):
        cx.ingest_manifest(self.db, MSORT_O2)
        v = cx.problem_view(self.db, "programs/msort/O2")
        self.assertTrue(all(o["status"] == "unsupported" for o in v["obligations"]))
        self.assertEqual([t["status"] for t in v["tests"]], ["passed"])
        self.assertEqual({q["status"] for k, q in v["questions"].items() if q and k != "edges"}, {"unsupported"})
        self.assertEqual(v["questions"]["edges"]["proved"], 0)
        cx.ingest_manifest(self.db, LOOP_O0)
        self.assertEqual(set(self.statuses("compiles-to/loop/O0/sum_to").values()), {"unsupported"})

    def test_execution_test_compares_with_the_expected_output(self):
        m = json.loads(MSORT_O2.read_bytes())
        m["tests"][0]["expected_stdout"] = "8 7 6 5 4 3 2 1\n"
        cx.ingest_manifest(self.db, self.write("m.json", m))
        self.assertEqual([t["status"] for t in cx.problem_view(self.db, "programs/msort/O2")["tests"]], ["failed"])

    def test_reingest_is_idempotent_and_migrations_rerun(self):
        a = cx.ingest_manifest(self.db, STRAIGHT_O0)
        b = cx.ingest_manifest(self.db, STRAIGHT_O0)
        self.assertEqual(a, b)
        cx.migrate(self.db)
        self.assertEqual([r[0] for r in self.db.execute("SELECT version FROM schema_migrations")], [1, 2, 3])

    def test_migration_keeps_existing_data(self):
        path = str(self.tmp / "old.sqlite")
        old = sqlite3.connect(path)
        old.execute("CREATE TABLE schema_migrations (version INTEGER PRIMARY KEY)")
        old.executescript("BEGIN;" + cx.MIGRATIONS[0] + "INSERT INTO schema_migrations VALUES (1); COMMIT;")
        old.close()
        db = cx.connect(path)  # migrates 2 and 3
        vid = cx.ingest_manifest(db, STRAIGHT_O0)
        self.assertEqual([r[0] for r in db.execute("SELECT version FROM schema_migrations")], [1, 2, 3])
        self.assertTrue(db.execute("SELECT row FROM obligations WHERE version_id = ? AND id = 'translation'",
                                   (vid,)).fetchone()[0])
        db.close()

    def test_artifacts_are_immutable(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        with self.assertRaises(sqlite3.IntegrityError):
            with self.db:
                sha = self.db.execute("SELECT sha256 FROM artifacts LIMIT 1").fetchone()[0]
                self.db.execute("INSERT INTO artifacts VALUES (?, 1, x'00')", (sha,))


class ManyToMany(Base):
    def test_inlined_line_maps_to_several_ranges_and_functions(self):
        cx.ingest_manifest(self.db, MSORT_O2)
        v = cx.problem_view(self.db, "programs/msort/O2")
        src = v["texts"]["source"].split("\n")
        line8 = [e for e in v["edges"] if e["id"].endswith("/8")]
        # `merge` is inlined: its line 8 has code in `msort` (and possibly in `main`)
        self.assertTrue(any(e["function"] == "msort" for e in line8))
        self.assertIn("tmp[k++] = (a[i] <= a[j])", src[7])
        frag = v["fragments"][line8[0]["target"][0]]
        self.assertGreater(len(frag["ranges"]), 1, "a discontiguous target fragment")
        # the call `merge(a, tmp, lo, mid, hi);` (line 24) has no code of its own once inlined
        lines_with_edges = {int(e["id"].rsplit("/", 1)[1]) for e in v["edges"]}
        self.assertNotIn(24, lines_with_edges)

    def test_duplicated_line_in_several_functions(self):
        lisp = MANIFESTS / "programs--lisp--O2.json"
        cx.ingest_manifest(self.db, lisp)
        v = cx.problem_view(self.db, "programs/lisp/O2")
        by_src = {}
        for e in v["edges"]:
            for f in e["source"]:
                by_src.setdefault(f, set()).add(e["function"])
        # `cons` (and `mk`) are inlined into both `read` and `eval`: one source line, two copies
        self.assertTrue(any(len(fns) > 1 for fns in by_src.values()))
        self.assertIn("/usr/include/x86_64-linux-gnu/bits/stdio.h",
                      v["extra"]["navigation_stats"]["instructions_from_other_files"])

    def test_navigation_and_semantic_edges_are_distinct(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        v = cx.problem_view(self.db, "compiles-to/straight/O0/add3")
        kinds = {e["kind"] for e in v["edges"]}
        self.assertEqual(kinds, {"navigation", "semantic"})
        for o in v["obligations"]:
            if o["edge"]:
                self.assertTrue(o["edge"].startswith("seg/"), "obligations attach to semantic edges only")

    def test_fragment_ids_are_content_addresses(self):
        m = json.loads(STRAIGHT_O0.read_bytes())
        src = m["artifacts"]["source"]["sha256"]
        f = next(f for f in m["fragments"] if f["artifact"] == "source")
        self.assertEqual(f["id"], cx.fragment_id(src, f["space"], f["ranges"]))


class Rejections(Base):
    def manifest(self, edit) -> pathlib.Path:
        m = json.loads(STRAIGHT_O0.read_bytes())
        edit(m)
        return self.write("m.json", m)

    def assertRejected(self, path, fn=None):
        with self.assertRaises(cx.Rejected):
            (fn or cx.ingest_manifest)(self.db, path)
        self.assertTrue(self.rejections())

    def test_statement_must_be_the_template(self):
        def edit(m):
            o = next(o for o in m["obligations"] if o["id"] == "edge/1")
            o["statement"] = "True"
            o["decl"] = "trivial"
        self.assertRejected(self.manifest(edit))

    def test_edge_statement_about_another_point(self):
        def edit(m):
            a = next(o for o in m["obligations"] if o["id"] == "edge/1")
            b = next(o for o in m["obligations"] if o["id"] == "edge/2")
            a["statement"] = b["statement"]
        self.assertRejected(self.manifest(edit))

    def test_forged_fragment_id(self):
        def edit(m):
            m["fragments"][0]["ranges"][0][1] += 1
        self.assertRejected(self.manifest(edit))

    def test_receipt_about_other_bytes(self):
        def edit(m):
            m["artifacts"]["receipt"] = m["artifacts"]["listing_receipt"]
        self.assertRejected(self.manifest(edit))

    def test_registry_names_another_artifact(self):
        def edit(m):
            m["lean"]["registry"]["target"] = "silmaril.compiles_to.straight.o2.object"
        self.assertRejected(self.manifest(edit))

    def test_lean_names_must_be_identifiers(self):
        def edit(m):
            m["lean"]["vars"]["target_value"] = "True"
            for o in m["obligations"]:
                if o["kind"] == "artifact":
                    o["statement"] = "True"
        self.assertRejected(self.manifest(edit))
        self.assertRejected(self.manifest(lambda m: m["lean"]["vars"].update(fn="(fun _ => True) x")))

    def test_target_value_must_read_the_target(self):
        def edit(m):
            m["lean"]["vars"]["target_value"] = "silmaril.compiles_to.straight.o2.obj"
            for o in m["obligations"]:
                if o["kind"] == "artifact":
                    o["statement"] = o["statement"].replace(".o0.obj", ".o2.obj")
        self.assertRejected(self.manifest(edit))

    def test_statement_model_is_the_context_model(self):
        self.assertRejected(self.manifest(lambda m: m["lean"]["vars"].update(isa="Silmaril.X86.Open9.isa")))

    def test_view_names_artifacts(self):
        self.assertRejected(self.manifest(lambda m: m["view"].update(target="nope")))

    def test_duplicate_fragment(self):
        self.assertRejected(self.manifest(lambda m: m["fragments"].append(dict(m["fragments"][0]))))

    def test_symlink_out_of_the_repository(self):
        root = self.tmp / "root"
        root.mkdir()
        outside = self.tmp / "secret.txt"
        outside.write_text("secret")
        (root / "link.txt").symlink_to(outside)
        with self.assertRaises(ValueError):
            cx.read_artifact(root, {"path": "link.txt", "sha256": cx.sha256(b"secret"), "size": 6})

    def test_unknown_direction(self):
        self.assertRejected(self.manifest(lambda m: m.update(direction="guessed")))

    def test_artifact_path_escape(self):
        def edit(m):
            m["artifacts"]["source"]["path"] = "../etc/passwd"
        self.assertRejected(self.manifest(edit))

    def test_changed_source_bytes(self):
        root = self.tmp / "root"
        m = json.loads(STRAIGHT_O0.read_bytes())
        for ref in m["artifacts"].values():
            dst = root / ref["path"]
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(ROOT / ref["path"], dst)
        (root / "silmaril" / "compiles-to").mkdir(parents=True)
        shutil.copy(ROOT / "silmaril" / "artifacts.toml", root / "silmaril")
        shutil.copy(ROOT / "silmaril" / "compiles-to" / "straight.toml", root / "silmaril" / "compiles-to")
        cx.ingest_manifest(self.db, STRAIGHT_O0, root=root)  # the copies are the manifest's bytes
        src = root / m["artifacts"]["source"]["path"]
        src.write_text(src.read_text().replace("int t = s + c;", "int t = s - c;"))
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m2.json", dict(m, title="x")), root=root)


class Project(Base):
    """The adapter to a `sil project` database, on the real schema: the golden database of
    tools/silmaril-project/tests/project/ok, plus the rows of one build."""

    def project_db(self, edit=None) -> pathlib.Path:
        path = self.tmp / "project.sqlite"
        pdb = sqlite3.connect(path)
        pdb.executescript((ROOT / "tools" / "silmaril-project" / "tests" / "project" / "ok" /
                           "project.sql").read_text())
        m = json.loads(STRAIGHT_O0.read_bytes())
        fn = m["lean"]["vars"]["fn"]
        edges = {e["id"]: e for e in m["edges"]}
        shapes = {k: v[0] for k, v in cx.ROW_SHAPES["c-function-x86"].items()}
        for o in m["obligations"]:
            if not o.get("row"):
                continue
            row = o["row"]
            pdb.execute("INSERT INTO problems (sid, name, kind, decl, module, origin, detached) "
                        "VALUES (?, ?, 'prop', ?, 'CompilesToExamples.Explorer.Rows', 'local', 0)",
                        (cx.sha256(row.encode()), row, row))
            pdb.execute("INSERT INTO edges VALUES ('instance', ?, 0, ?, ?, 'instance', ?)",
                        (row, shapes[o["kind"]], row, row))
            point = edges[o["edge"]]["point"] if o.get("edge") else None
            args = cx.ROW_SHAPES["c-function-x86"][o["kind"]][1](m["lean"]["vars"], point)
            for i, a in enumerate(args):
                    pdb.execute("INSERT INTO instance_args VALUES (?, ?, ?, NULL, NULL)", (row, i, a))
            decl = row.replace("silmaril.", "Rows.")
            pdb.execute("INSERT INTO statuses VALUES (?, 'THM', 'solves', ?, 'kernel')", (row, decl))
            for ax in ("propext", "Classical.choice", "Quot.sound"):
                pdb.execute("INSERT INTO answer_axioms VALUES (?, ?)", (decl, ax))
        if edit:
            edit(pdb)
        pdb.commit()
        pdb.close()
        return path

    def test_rows_prove_with_artifact_binding(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_project(self.db, self.project_db())
        st = self.statuses("compiles-to/straight/O0/add3")
        for k in ("artifact", "translation", "mapping", "refinement", "nonvacuity", "edge/3"):
            self.assertEqual(st[k], "proved", k)
        self.assertEqual(st["abi"], "unchecked")  # no row, no exporter result

    def test_without_the_code_row_everything_is_unbound(self):
        def edit(pdb):
            pdb.execute("DELETE FROM statuses WHERE problem LIKE '%.code'")
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_project(self.db, self.project_db(edit))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["artifact"], "open")
        self.assertEqual(st["translation"], "unbound")

    def test_row_of_another_function_is_a_mismatch(self):
        def edit(pdb):
            pdb.execute("UPDATE instance_args SET term = 'CompilesToExamples.Branch.O0.max2' WHERE pos = 0")
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_project(self.db, self.project_db(edit))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["translation"], "rejected")

    def test_open_row_and_other_axioms(self):
        def edit(pdb):
            pdb.execute("DELETE FROM statuses WHERE problem LIKE '%.mapping'")
            pdb.execute("INSERT INTO answer_axioms SELECT via, 'sorryAx' FROM statuses WHERE problem LIKE '%.translation'")
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_project(self.db, self.project_db(edit))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["mapping"], "open")
        self.assertEqual(st["translation"], "rejected")

    def test_other_schema_is_refused(self):
        def edit(pdb):
            pdb.execute("UPDATE meta SET value = 'silmaril.project-db.v9' WHERE key = 'schema'")
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        with self.assertRaises(cx.Rejected):
            cx.ingest_project(self.db, self.project_db(edit))


class Directions(Base):
    DECOMPILED = MANIFESTS / "decompiled--scale.json"
    IMPORTED = MANIFESTS / "imported--sha256-compress.json"

    def test_decompiled_and_imported_are_ingested_without_claims(self):
        cx.ingest_manifest(self.db, self.DECOMPILED)
        cx.ingest_manifest(self.db, self.IMPORTED)
        v = cx.problem_view(self.db, "decompiled/scale")
        self.assertEqual(v["direction"], "decompiled")
        st = {o["id"]: o["status"] for o in v["obligations"]}
        self.assertEqual(st.pop("decompilation"), "unchecked")  # stated, not yet checked
        self.assertEqual(set(st.values()), {"unsupported"})
        v = cx.problem_view(self.db, "imported/sha256-compress")
        self.assertEqual({o["status"] for o in v["obligations"]}, {"unsupported"})

    def test_decompiled_block_must_be_the_objects_text(self):
        for edit in (lambda v: v.update(bytes=[0x48, 0x8d, 0x44, 0xfe, 0xfc]),
                     lambda v: v.update(inputs=[["rax", "a"], ["rsi", "b"]]),
                     lambda v: v.update(name="scale; int x")):
            m = json.loads(self.DECOMPILED.read_bytes())
            edit(m["lean"]["vars"])
            with self.assertRaises(cx.Rejected):
                cx.ingest_manifest(self.db, self.write("m.json", m))

    def test_decompiled_statement_is_about_the_source_text(self):
        m = json.loads(self.DECOMPILED.read_bytes())
        o = m["obligations"][0]
        o["statement"] = o["statement"].replace("8ULL", "9ULL")
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m.json", m))

    def test_lean_strings_are_escaped(self):
        self.assertEqual(cx.lean_str('a"b\\c\n'), '"a\\"b\\\\c\\n"')
        with self.assertRaises(ValueError):
            cx.lean_str("é")

    def test_decompiler_receipt_must_read_the_target(self):
        m = json.loads(self.DECOMPILED.read_bytes())
        m["artifacts"]["receipt"] = m["artifacts"]["compile_receipt"]
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m.json", m))

    def test_imported_cannot_claim_a_checked_derivation(self):
        m = json.loads(self.IMPORTED.read_bytes())
        m["derivation"] = {"kind": "compiler", "compiler": "clang", "version": "18.1.3"}
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m.json", m))

    def test_compiled_needs_a_receipt(self):
        m = json.loads(MSORT_O2.read_bytes())
        del m["derivation"]["receipt"]
        with self.assertRaises(cx.Rejected):
            cx.ingest_manifest(self.db, self.write("m.json", m))


class Binding(Base):
    def test_function_of_another_build_is_unbound(self):
        """The branch -O2 problem, its statements about straight.c's add3: theorems exist for
        them, but the add3 bytes are not branch.o's, so nothing is shown proved."""
        m = json.loads(BRANCH_O2.read_bytes())
        straight = json.loads(STRAIGHT_O0.read_bytes())
        m["lean"]["vars"]["fn"] = straight["lean"]["vars"]["fn"]
        m["lean"]["vars"]["cname"] = "add3"
        decls = {o["id"]: o["decl"] for o in straight["obligations"]}
        for o in m["obligations"]:
            e = next((e for e in m["edges"] if e["id"] == o.get("edge")), None)
            o["statement"] = cx.statement_for("c-function-x86", m["lean"]["vars"], o["kind"],
                                              e and e["point"], e and e.get("line"))
            o["decl"] = decls.get(o["id"])
        p = self.write("m.json", m)
        cx.ingest_manifest(self.db, p)
        # the exporter would find every theorem but the artifact one (add3 is not in branch.o)
        ev = evidence_for(p, lambda o: "mismatch" if o["kind"] == "artifact" else "kernel")
        self.trusted(self.write("ev.json", ev))
        st = self.statuses("compiles-to/branch/O2/max2")
        self.assertEqual(st["artifact"], "rejected")
        self.assertEqual(st["translation"], "unbound")
        self.assertNotIn("proved", st.values())


class Evidence(Base):
    def test_handed_in_file_is_only_a_claim(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        cx.ingest_evidence(self.db, self.write("ev.json", evidence_for(STRAIGHT_O0)))
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["translation"], "claimed")
        self.assertNotIn("proved", st.values())

    def test_duplicate_obligation(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0, edit=lambda e: e["obligations"].append(dict(e["obligations"][0])))
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", ev))

    def test_unknown_manifest(self):
        p = self.write("ev.json", evidence_for(STRAIGHT_O0))
        with self.assertRaises(cx.Rejected):
            cx.ingest_evidence(self.db, p)  # the manifest was never ingested

    def test_statement_differs(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0, edit=lambda e: e["obligations"][0].update(statement="True"))
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", ev))

    def test_kernel_without_declaration(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)

        def edit(e):
            o = next(o for o in e["obligations"] if o["id"] == "nonvacuity/universal")
            o["status"] = "kernel"
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", evidence_for(STRAIGHT_O0, edit=edit)))

    def test_non_standard_axiom(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)

        def edit(e):
            e["obligations"][0]["axioms"] = ["sorryAx"]
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", evidence_for(STRAIGHT_O0, edit=edit)))

    def test_other_modules(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        ev = evidence_for(STRAIGHT_O0, edit=lambda e: e.update(modules=["Other"]))
        with self.assertRaises(cx.Rejected):
            self.trusted(self.write("ev.json", ev))

    def test_evidence_does_not_carry_to_a_new_version(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        self.trusted(self.write("ev.json", evidence_for(STRAIGHT_O0)))
        m = json.loads(STRAIGHT_O0.read_bytes())
        m["context"]["target_model"]["version"] = "another x86-64 model version"
        p2 = self.write("m2.json", m)
        cx.ingest_manifest(self.db, p2)
        st = self.statuses("compiles-to/straight/O0/add3")
        self.assertEqual(st["translation"], "stale")
        self.assertEqual(st["nonvacuity/universal"], "open")
        v = cx.problem_view(self.db, "compiles-to/straight/O0/add3")
        self.assertEqual(len(v["versions"]), 2)
        # the old evidence file cannot be replayed against the new manifest
        with self.assertRaises(cx.Rejected):
            ev = evidence_for(STRAIGHT_O0)
            ev["manifest_sha256"] = cx.sha256(p2.read_bytes())
            ev["obligations"][0]["statement"] += " "
            self.trusted(self.write("ev2.json", ev))
        self.trusted(self.write("ev3.json", evidence_for(p2)))
        self.assertEqual(self.statuses("compiles-to/straight/O0/add3")["translation"], "proved")


class QuietHandler(cx.Handler):
    def log_message(self, fmt, *args):
        pass


class Server(Base):
    def test_read_only_api(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        self.db.commit()
        QuietHandler.db_path = str(self.tmp / "t.sqlite")
        srv = cx.http.server.ThreadingHTTPServer(("127.0.0.1", 0), QuietHandler)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
        try:
            def req(method, path):
                c = http.client.HTTPConnection("127.0.0.1", srv.server_address[1])
                c.request(method, path)
                r = c.getresponse()
                out = r.status, r.getheader("Content-Security-Policy"), r.read()
                c.close()
                return out
            st, csp, body = req("GET", "/api/problems")
            self.assertEqual(st, 200)
            self.assertIn("default-src 'self'", csp)
            self.assertEqual(json.loads(body)[0]["id"], "compiles-to/straight/O0/add3")
            st, _, body = req("GET", "/api/problems/compiles-to%2Fstraight%2FO0%2Fadd3")
            self.assertEqual(json.loads(body)["questions"]["translation"]["status"], "unchecked")
            self.assertEqual(req("POST", "/api/problems")[0], 405)
            self.assertEqual(req("GET", "/../cexplorer.py")[0], 404)
            self.assertEqual(req("GET", "/api/compile")[0], 404)
            self.assertEqual(req("GET", "/api/problems/nope")[0], 404)
        finally:
            srv.shutdown()
            srv.server_close()

    def test_readonly_connection(self):
        cx.ingest_manifest(self.db, STRAIGHT_O0)
        self.db.commit()
        ro = cx.connect(str(self.tmp / "t.sqlite"), readonly=True)
        with self.assertRaises(sqlite3.OperationalError):
            ro.execute("DELETE FROM evidence")
        ro.close()


if __name__ == "__main__":
    unittest.main(verbosity=1)
