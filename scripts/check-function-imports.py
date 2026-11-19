#!/usr/bin/env python3
"""Keep both function-relation closures free of concrete adapters."""

import pathlib
import re


IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(Silmaril\.[\w.]+)\b", re.M)


def check(root, allowed):
    pending = [(".".join(path.with_suffix("").parts), ()) for path in pathlib.Path(root).rglob("*.lean")]
    seen = set()
    failures = []
    while pending:
        module, chain = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        chain = (*chain, module)
        region = module.removeprefix("Silmaril.").removeprefix("Proofs.").removeprefix("Raw.").split(".")[0]
        if region not in allowed:
            failures.append(" -> ".join(chain))
            continue
        source = pathlib.Path(module.replace(".", "/") + ".lean").read_text()
        pending.extend((imported, chain) for imported in IMPORT.findall(source))
    return failures


errors = check("Silmaril/Semantics/Function", {"Semantics", "Prelude"})
errors += check("Silmaril/Logic/Function", {"Logic", "Semantics", "Prelude"})
for error in errors:
    print(f"concrete function API import: {error}")
raise SystemExit(bool(errors))
