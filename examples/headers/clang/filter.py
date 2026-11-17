#!/usr/bin/env python3
"""Filter a clang `-ast-dump=json` translation unit to the declarations of named files.

    python3 -I filter.py FILE... < full.json > filtered.json

FILE are the file names as clang prints them in locations (`arith.h`, `../common/rt.h`,
`./zconf.h`). The filter is part of the recipe (`recipe.sh`) and is recorded with it. It does
exactly four things and nothing else:

1. **Selection.** A top-level node of the TranslationUnitDecl is kept iff the file of its
   `loc` is one of FILE. For a location inside a macro expansion the file is that of the
   *expansion* location (where the declaration is written), not of the macro's spelling. A
   node whose `loc` is empty (clang's implicit builtin typedefs) has no file and is dropped.
   The order of the kept nodes is clang's.
2. **Delta locations made explicit.** Clang prints a location's `file` only when it differs
   from the previously printed location, and its `line` only when the file or the line
   differs (JSONNodeDumper::writeBareSourceLocation). Dropping nodes would break that chain,
   so in the first non-empty location of each kept node the omitted `file` and `line` are
   inserted, with the values the full document gives them (`file` after `offset`, `line`
   after `file`, as clang orders them). Every other location is unchanged, and inside a kept
   node the chain is then the one clang printed.
3. **Ids renumbered.** Clang's node ids are heap addresses and differ from run to run. Every
   string under one of the keys in `ID_KEYS` (anywhere in the document, including references
   to dropped nodes) is replaced by `0x` followed by the hexadecimal index of its first
   appearance (in the output document order, starting at 1). Equal ids stay equal and
   different ids stay different.
4. **Layout.** The output is compact JSON (no spaces), with the root's `inner` written one
   kept node per line, and a final newline. Keys keep clang's order.

Nothing inside a kept node is otherwise changed: no key is removed, renamed or reordered.
"""
import json
import sys

ID_KEYS = {"id", "previousDecl", "parentDeclContextId", "typeAliasDeclId", "declId",
           "referencedMemberDecl", "targetLabelDeclId"}


class Chain:
    """The delta-encoding state of clang's location printer."""

    def __init__(self):
        self.file = None
        self.line = None

    def bare(self, loc, fill):
        """Advance over one bare location; if `fill`, make its file and line explicit.
        Returns (file, whether it was non-empty, the location to print)."""
        if not loc:
            return None, False, loc
        if "file" in loc:
            self.file = loc["file"]
        if "line" in loc:
            self.line = loc["line"]
        if fill and ("file" not in loc or "line" not in loc):
            out = {}
            for k, v in loc.items():
                out[k] = v
                if k == "offset":
                    out["file"] = self.file
                    out["line"] = self.line
                elif k == "file" and "line" not in loc:
                    out["line"] = self.line
            for k in ("file", "line"):
                if k not in out:
                    raise SystemExit("filter: location without offset")
            # keep clang's key order: offset, file, line, then the rest
            loc = {k: out[k] for k in ["offset", "file", "line"]} | \
                {k: v for k, v in out.items() if k not in ("offset", "file", "line")}
        return self.file, True, loc

    def loc(self, loc, fill):
        """A location (bare, or macro with spelling and expansion). Returns
        (file of the expansion, whether a non-empty bare location was seen, location)."""
        if "spellingLoc" in loc:
            out = dict(loc)
            _, seen, out["spellingLoc"] = self.bare(loc["spellingLoc"], fill)
            f, seen2, out["expansionLoc"] = self.bare(loc["expansionLoc"], fill and not seen)
            return f, seen or seen2, out
        return self.bare(loc, fill)


def walk(node, chain, fill):
    """Advance the chain over a node in print order; fill the first location if `fill`.
    Returns (file of the node's own loc, the node to print, whether still to fill)."""
    if not isinstance(node, dict):
        return None, node, fill
    out = {}
    own = None
    for k, v in node.items():
        if k == "loc":
            own, seen, v = chain.loc(v, fill)
            fill = fill and not seen
        elif k == "range":
            r = {}
            for kk, vv in v.items():
                _, seen, r[kk] = chain.loc(vv, fill)
                fill = fill and not seen
            v = r
        elif k in ("inner", "array_filler"):
            kids = []
            for c in v:
                _, c, fill = walk(c, chain, fill)
                kids.append(c)
            v = kids
        out[k] = v
    return own, out, fill


def renumber(x, table):
    if isinstance(x, dict):
        return {k: (table.setdefault(v, "0x%x" % (len(table) + 1))
                    if k in ID_KEYS and isinstance(v, str) else renumber(v, table))
                for k, v in x.items()}
    if isinstance(x, list):
        return [renumber(v, table) for v in x]
    return x


def main():
    files = set(sys.argv[1:])
    tu = json.load(sys.stdin)
    if tu.get("kind") != "TranslationUnitDecl":
        raise SystemExit("filter: not a TranslationUnitDecl")
    chain = Chain()
    kept = []
    for node in tu.get("inner", []):
        # Selection needs the node's file before deciding to fill: walk twice over a copy
        # of the chain state.
        saved = (chain.file, chain.line)
        own, _, _ = walk(node, chain, False)
        if own in files:
            chain.file, chain.line = saved
            _, filled, _ = walk(node, chain, True)
            kept.append(filled)
    root = {k: v for k, v in tu.items() if k != "inner"}
    table = {}
    root = renumber(root, table)
    kept = [renumber(n, table) for n in kept]
    dump = lambda v: json.dumps(v, separators=(",", ":"), ensure_ascii=True)
    head = dump(root)[:-1]
    body = ",\n".join(dump(n) for n in kept)
    sys.stdout.write(head + ',"inner":[\n' + body + "\n]}\n")


if __name__ == "__main__":
    main()
