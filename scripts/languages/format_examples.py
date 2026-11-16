#!/usr/bin/env python3
"""Generate examples/project/ProjectSelfTest/FormatExamples.lean.

Every `example : W ∈ L` / `example : W ∉ L` of the byte-language modules of `Silmaril/Formats`
(listed in FILES) becomes a registered language (`silmaril language … (op := decl)`, one per
distinct `L` of a file, so each profile is its own language) and a closed instance of
`silmaril.shapes.language.member` with `expect` THM (∈) or CSA (∉) and an answer whose proof is
the example's own proof, restated in the example's namespace. Nothing is inferred: an example
attaches only to the language it is written about.

    python3 -I scripts/languages/format_examples.py            # rewrite the file
    python3 -I scripts/languages/format_examples.py --check    # fail if it is out of date
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / "examples/project/ProjectSelfTest/FormatExamples.lean"
# (module file, short name, title of the group). JsonEvents' examples are about event streams
# of its local `sample` tree, not byte strings; they are not restated here.
FILES = [
    ("Silmaril/Formats/Ascii/Thms.lean", "ascii", "ASCII"),
    ("Silmaril/Formats/Utf16/Thms.lean", "utf16", "UTF-16"),
    ("Silmaril/Formats/JsonBytes/Thms.lean", "json", "JSON texts (RFC 8259)"),
    ("Silmaril/Formats/JsonBytes/Decide/Thms.lean", "json.decide", "JSON texts, decided (RFC 8259)"),
    ("Silmaril/Formats/JsonBytes/Depth/Thms.lean", "json.depth", "JSON texts of bounded depth (RFC 8259 §9)"),
    ("Silmaril/Formats/JsonNumbers/Thms.lean", "json.numbers", "JSON numbers"),
    ("Silmaril/Formats/JsonLines/Thms.lean", "jsonl", "JSON Lines and NDJSON"),
    ("Silmaril/Formats/Cbor/WellFormed/Thms.lean", "cbor.wellformed", "Well-formed CBOR (RFC 8949)"),
    ("Silmaril/Formats/Cbor/ModelValid/Thms.lean", "cbor.model_valid", "CBOR valid relative to Cbor.Value"),
    ("Silmaril/Formats/Cbor/Deterministic/Thms.lean", "cbor.deterministic", "Deterministic CBOR (float rule as a parameter)"),
    ("Silmaril/Formats/Cbor/Drisl/Thms.lean", "cbor.drisl", "DRISL, BDASL, no-links and ATProto-core profiles"),
    ("Silmaril/Formats/Spki/Thms.lean", "spki", "Canonical SPKI S-expressions (RFC 9804)"),
]
JSON_HEAD = ("(first\n"
    "    | exact (Silmaril.Formats.JsonBytes.mem_language_iff_rmatch_of_head (by decide) (by decide) (by decide)).mpr\n"
    "        (by decide +kernel)\n"
    "    | exact fun h => absurd ((Silmaril.Formats.JsonBytes.mem_language_iff_rmatch_of_head (by decide) (by decide)\n"
    "        (by decide)).mp h) (by decide +kernel))")

def slug(s):
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", s).lower()
    s = re.sub(r"[^a-z0-9]+", "_", s).strip("_")
    return s or "lang"

def seg(s):
    s = slug(s)
    return s if s[0].isalpha() else "l" + s

class _M:
    def __init__(self, a, b): self.g = (None, a, b)
    def group(self, i): return self.g[i]

def split_example(block):
    """`example : STMT := PROOF`, splitting at the first `:=` outside brackets."""
    m = re.match(r"example\s*:\s*", block)
    if not m:
        return None
    body, depth = block[m.end():], 0
    for i, c in enumerate(body):
        if c in "({[":
            depth += 1
        elif c in ")}]":
            depth -= 1
        elif depth == 0 and body.startswith(":=", i):
            return _M(body[:i].strip(), body[i + 2:].strip())
    return None

def examples(text):
    """(line, comment, statement, proof) of each membership example."""
    lines = text.split("\n")
    out, i = [], 0
    while i < len(lines):
        if lines[i].startswith("example"):
            j = i + 1
            while j < len(lines) and lines[j].startswith(("  ", "\t")):
                j += 1
            block = "\n".join(lines[i:j])
            block = re.sub(r"\s*--[^\n]*", "", block)   # trailing comments
            m = split_example(block)
            prev = lines[i - 1].strip() if i else ""
            comment = prev[2:].strip() if prev.startswith("--") else ""
            tail = re.search(r"--\s*(.*)$", lines[i])
            if tail and not comment:
                comment = tail.group(1).strip()
            if m and ("∈" in m.group(1) or "∉" in m.group(1)):
                stmt, proof = m.group(1), m.group(2).strip()
                mm = re.match(r"(.*?)\s+(∈|∉)\s+(.*)$", " ".join(stmt.split()))
                if mm:
                    out.append((i + 1, comment, mm.group(1), mm.group(2), mm.group(3), proof))
            i = j
        else:
            i += 1
    return out

def context(text):
    """The namespace of the examples, with its ancestors opened (as inside the namespace), and
    the file's `open`s."""
    ns = re.findall(r"^namespace (\S+)", text, re.M)[0]
    parts = ns.split(".")
    ancestors = [".".join(parts[:k]) for k in range(2, len(parts))]
    opens = [o for o in re.findall(r"^open (?!scoped)(.+)$", text, re.M)]
    return " ".join(ancestors + [ns]), opens

def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'

def generate():
    o = ["module", "",
         "public import Silmaril.Project.Shapes.Language.Thms"]
    for f, _, _ in FILES:
        o.append("public import " + f[:-5].replace("/", "."))
    o += ["", "/-!", "# Format languages and their examples (generated)", "",
          "Generated by `scripts/languages/format_examples.py` from the membership examples of the format",
          "modules; do not edit. Each distinct language of a module (a profile, a depth, a policy) is",
          "one registered language, and each example is a closed instance of",
          "`silmaril.shapes.language.member` about exactly that language: THM for `∈`, UNS for `∉`,",
          "with the example's own proof. JsonEvents' examples are about event streams of a local tree",
          "and are not restated.", "",
          "**Stable names.** A language term `L` of module `M` is the definition",
          "`Silmaril.Project.Languages.FormatExamples.<M>.lang_<snake L>` and the language",
          "`formats.<m>.<snake L>`; the same term always gets the same name (a clash in one module takes",
          "a `_` suffix, in file order). Problems are `formats.examples.<m>.l<line>`, by source line.",
          "-/", "",
          "/-- `json_head` of `Silmaril/Formats/JsonBytes/Thms.lean`: decide a text that starts with a",
          "byte other than whitespace, `[` and `{`. -/",
          "local macro \"json_head\" : tactic =>", "  `(tactic| " + JSON_HEAD + ")", ""]
    groups, top = [], []
    for f, short, title in FILES:
        text = (ROOT / f).read_text()
        ns, opens = context(text)
        exs = examples(text)
        if not exs:
            continue
        langs = {}
        for ex in exs:
            langs.setdefault(ex[4], None)
        o.append(f"/-! ## {title} (`{f}`) -/\n")
        o.append(f"namespace Silmaril.Project.Languages.FormatExamples.{''.join(p.capitalize() for p in re.split(r'[._]', short))}")
        o.append("open " + ns + (" " + " ".join(opens) if opens else ""))
        o.append("@[expose] public section")
        # Stable public names: the definition `lang_<term>` and the language `formats.<module>.<term>`
        # are named after the language term (deterministic: the same term gives the same name; a clash takes a `_` suffix in
        # file order).
        names, taken = {}, set()
        for L in langs:
            d = "lang_" + slug(L)
            while d in taken:
                d += "_"
            taken.add(d)
            names[L] = (d, f"formats.{short}.{d[len('lang_'):]}")
            o.append(f"/-- `{L}` (`{f}`) -/\ndef {d} := {L}")
        o.append("end")
        nsfull = o[-len(langs) * 1 - 3].split(" ", 1)[1] if False else None
        o.append(f"end Silmaril.Project.Languages.FormatExamples.{''.join(p.capitalize() for p in re.split(r'[._]', short))}\n")
        nsname = f"Silmaril.Project.Languages.FormatExamples.{''.join(p.capitalize() for p in re.split(r'[._]', short))}"
        for L, (d, lname) in names.items():
            o.append(f"silmaril language {lname} := {nsname}.{d} (domain := bytes) (op := decl)\n"
                     f"  (title := {lean_str(L)}) (source := {lean_str(f)})")
        o.append("")
        kids = []
        for n, (line, comment, w, rel, L, proof) in enumerate(exs):
            d, lname = names[L]
            pname = f"formats.examples.{short}.l{line}"
            kids.append(pname)
            # a closed refutation is recorded as UNS (`@[refutes]`), so that is what a `∉` example
            # expects; CSA follows from it at arity 0, but the summary is UNS
            expect = "THM" if rel == "∈" else "UNS"
            status = "thm" if rel == "∈" else "csa"
            title = f"{w} {rel} {L}" + (f" — {comment}" if comment else "")
            o.append(f"silmaril instance {pname} (expect := {expect}) (title := {lean_str(title)})\n"
                     f"  (doc := {lean_str(f'{f}:{line}')}) := silmaril.shapes.language.member\n"
                     f"  (L := {nsname}.{d}) (x := ({w} : List UInt8))")
            o.append(f"namespace {nsname}\nopen {ns}" + (" " + " ".join(opens) if opens else ""))
            o.append(f"theorem ex{line} : {w} {rel} {L} := {proof}")
            neg = "¬ " if rel == "∉" else ""
            o.append(f"@[answers \"{pname}\" {status}] public theorem ans{line} :\n"
                     f"    {neg}Silmaril.Project.Shapes.Member {d} ({w} : List UInt8) := ex{line}")
            o.append(f"end {nsname}\n")
        gname = f"formats.examples.{short}"
        groups.append(gname)
        o.append(f"silmaril group {gname} (title := {lean_str(title + ': examples')})\n  (children := [{', '.join(kids)}])\n")
    o.append(f"silmaril group formats.examples (title := \"Examples of the format languages\")\n  (children := [{', '.join(groups)}])")
    return "\n".join(o) + "\n"

if __name__ == "__main__":
    text = generate()
    if "--check" in sys.argv:
        if OUT.read_text() != text:
            sys.exit(f"{OUT} is out of date: run {sys.argv[0]}")
    else:
        OUT.write_text(text)
        print(f"wrote {OUT}")
