# SPDX-License-Identifier: MIT
"""Check published closure operands, their evaluation order, and receipt attribution."""

from pathlib import Path
import runpy
import sys
import tempfile

PREFIX = """marker = 37
def inner():
    value = 3
    def keep():
        return value
    return 0
alias = inner
inner = 99
"""

SUCCESS = PREFIX + """def second():
    value = 5
    def keep():
        return value
    return 0
___assertEqual(alias(), second())
"""
LEFT = PREFIX + "___assertEqual(alias(), later_missing)\n"
ARITY = PREFIX + "___assertEqual(alias(3), later_missing)\n"
INPUT = PREFIX + "___assertEqual(alias(first_missing), later_missing)\n"
MASK = PREFIX + "___assertEqual(inner(1), later_missing)\n"
BODY = PREFIX.replace("return 0", "return body_missing") + "___assertEqual(alias(), later_missing)\n"
TUPLE = PREFIX.replace("return 0", "return (value, None, True)") + "___assertEqual(alias(), alias())\n"

LEAN = r"""
open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions.Run
open Core.Module.SeededCall (Namespace Result)

private def check (source : Source.Module) (expected : Except Seeded.ModuleFailure Unit)
    (owned : List Int) (receipts : List (String × Result)) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let .finished plain (.raised (.nameError "___assertEqual")) :=
    (runPrefix compiled.table 100 compiled.start).2 | return false
  let empty := Seeded.run .empty compiled
  let spaces := [Seeded.legacySeed .builtin, Seeded.legacySeed .preamble]
  return plain.heap.next == 0 && empty.heap.next == 0 && empty.calls.isEmpty &&
    empty.completion == .error (.raised (.runtime (.nameError "___assertEqual"))) &&
    spaces.all fun space =>
      let observed := Seeded.run space compiled
      let cells := (List.range observed.heap.next).map (fun i => (observed.heap.contents i).map Seeded.seededValue)
      observed.completion == expected && cells == owned.map (some ∘ .int) &&
      observed.residual.builtins == space.builtins && observed.residual.lookupGlobal "marker" == some (.int 37) &&
      observed.residual.lookupGlobal "inner" == some (.int 99) &&
      observed.calls.map (fun event => (event.callee, event.observation.result)) == receipts &&
      observed.calls.all (fun event => event.observation.caught.isNone)

private def interrupted (source : Source.Module) : Bool := Id.run do
  let .ok compiled := compile source | return false
  let observed := Seeded.run (Seeded.legacySeed .builtin) compiled .empty 2
  let some (.function closure) := observed.residual.lookupGlobal "alias" | return false
  let arguments := [(.int 3 : Core.Module.SeededCall.Value)]
  let context : Seeded.CallContext := { table := compiled.table, heap := .empty, fuel := 10 }
  let declined := Seeded.argumentObservation "alias" <|
    Seeded.invokePublishedArgument observed.residual context closure arguments
  let arity := Seeded.argumentObservation "alias" <|
    Seeded.invokePublishedArgument observed.residual { context with published := [closure] } closure arguments
  let fault := Seeded.argumentObservation "alias" <|
    Seeded.invokePublishedArgument observed.residual { context with table := fun _ => none, published := [closure] }
      closure []
  return observed.completion == .error .directCallFuelExhausted && observed.calls.isEmpty &&
    observed.heap.next == 1 && (observed.heap.contents 0).map Seeded.seededValue == some (.int 3) &&
    declined.1 == .error .unsupported && declined.2.2.next == 0 &&
    arity.1 == .error (.raised (.runtime (.positionalArity 0 1))) && arity.2.1.length == 1 &&
    arity.2.2.next == 0 && fault.1 == .error (.directCallFault (.missingCode closure.code.key)) && fault.2.1.isEmpty
"""


def observe(source, expected, name, reached):
    def compare(left, right):
        assert left == right

    actual = []
    def track(frame, event, _):
        if event == "return" and frame.f_code.co_name in ("inner", "second"):
            actual.append(frame.f_locals["value"])

    for namespace in ({"__builtins__": {"___assertEqual": compare}},
                      {"__builtins__": {}, "___assertEqual": compare}):
        actual.clear()
        sys.setprofile(track)
        try:
            exec(compile(source, "<nested call operands>", "exec", dont_inherit=True, optimize=0), namespace)
        except (TypeError, NameError) as error:
            assert type(error) is expected and getattr(error, "name", None) == name
        else:
            assert expected is None
        finally:
            sys.setprofile(None)
        assert actual == reached and namespace["inner"] == 99 and namespace["marker"] == 37


def main():
    assert sys.version_info[:3] == (3, 13, 5)
    root = Path(__file__).resolve().parents[1] / "tests/languages/python"
    shared = runpy.run_path(str(root / "source-scope/check_intake.py"))
    imports = runpy.run_path(str(root / "source-module-entry/check_return_local_call.py"))["IMPORTS"]
    observe(ARITY, TypeError, None, [])
    fixtures = [
        (SUCCESS, None, None, [3, 5], '(.ok ()) [3, 5] '
         '[("alias", .ok (.int 0)), ("second", .ok (.int 0)), ("___assertEqual", .ok .none)]'),
        (LEFT, NameError, "later_missing", [3],
         '(.error (.raised (.runtime (.nameError "later_missing")))) [3] [("alias", .ok (.int 0))]'),
        (INPUT, NameError, "first_missing", [], '(.error (.raised (.runtime (.nameError "first_missing")))) [] '
         '[("alias", .error (.raised (.runtime (.nameError "first_missing"))))]'),
        (MASK, TypeError, None, [], '(.error (.raised (.runtime .notCallable))) [] '
         '[("inner", .error (.raised (.runtime .notCallable)))]'),
        (BODY, NameError, "body_missing", [3], '(.error (.raised (.runtime (.nameError "body_missing")))) [3] '
         '[("alias", .error (.raised (.runtime (.nameError "body_missing"))))]'),
        (TUPLE, None, None, [3, 3], '(.ok ()) [3, 3] '
         '[("alias", .ok (.returnedTuple [.int 3, .none, .bool true])), '
         '("alias", .ok (.returnedTuple [.int 3, .none, .bool true])), ("___assertEqual", .ok .none)]'),
    ]
    with tempfile.TemporaryDirectory() as directory:
        raw, lean = Path(directory) / "Nested.py", Path(directory) / "Nested.lean"
        chunks = []
        for index, (source, error, name, reached, arguments) in enumerate(fixtures):
            observe(source, error, name, reached)
            shared["emit"](raw, lean, source)
            header, declaration = lean.read_text().split("public def pythonSource", 1)
            interrupt = "#guard interrupted pythonSource\n" if index == 0 else ""
            chunks.append(f"namespace Case{index}\npublic def pythonSource{declaration}\n"
                          f"#guard check pythonSource {arguments}\n{interrupt}end Case{index}\n")
        lean.write_text(header + LEAN + "\n".join(chunks))
        shared["check_lean"](lean, "", extra_imports=imports)
    print("CPython 3.13.5 and Lean checked live nested call operands, order, and receipt attribution.")


if __name__ == "__main__":
    main()
