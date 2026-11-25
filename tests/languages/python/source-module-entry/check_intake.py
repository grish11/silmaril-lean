# SPDX-License-Identifier: MIT
"""Check the source module-entry profile through actual Python AST emission."""

from pathlib import Path
import runpy
import tempfile


LEAN = """
open Silmaril.Languages.Python.Compile.ModuleEntry

private def describe {scope : Scope} : Operand scope → String
  | .integer value => toString value
  | .read name reference =>
    match reference.access with
    | .declaredGlobal => "declared read " ++ name
    | .moduleName => "module read " ++ name
    | _ => "wrong access"

private def action {scope : Scope} : Action scope → String
  | .assign name reference value =>
    let accessDescription := match reference.access with
      | .declaredGlobal => "declared write "
      | .moduleName => "module write "
      | _ => "wrong access "
    accessDescription ++ name ++ ": " ++ describe value
  | .assertion condition => "assert: " ++ describe condition

private def actions (source : Module) : Option (List String) :=
  (check source).toOption.map fun compiled => compiled.actions.map action
"""


if __name__ == "__main__":
    shared = runpy.run_path(str(Path(__file__).resolve().parent.parent / "source-scope/check_intake.py"))
    imports = (
        "import Silmaril.Languages.Python.Compile.ModuleEntry.Thms",
        "meta import Silmaril.Languages.Python.Compile.ModuleEntry.Defs",
    )
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "Example.py"
        generated = Path(tmp) / "Example.lean"
        shared["emit"](source, generated, """
global exposed
exposed = 3
ordinary = exposed
assert ordinary
pass
assert missing
""")
        shared["check_lean"](generated, LEAN + """
#guard actions pythonSource == some
  ["declared write exposed: 3", "module write ordinary: declared read exposed",
    "assert: module read ordinary", "assert: module read missing"]

#print axioms global_reference
#print axioms statements_complete
#print axioms check_complete
""", extra_imports=imports)
        shared["emit"](source, generated, 'assert 0, "message"\n')
        shared["check_lean"](generated, LEAN + """
#guard (match check pythonSource with | .error .assertionMessage => true | _ => false)
""", extra_imports=imports)
