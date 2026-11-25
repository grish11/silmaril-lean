module

public import Silmaril.Languages.Python.Core.Module.SeededCall.Defs
import Silmaril.Proofs.Languages.Python.Core.Module.SeededCall.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Module.SeededCall

theorem Namespace.module_precedes (space : Namespace) {name : String} {value : Value}
    (found : lookupBinding space.moduleGlobals name = some value) : space.lookupGlobal name = some value := by
  simp [Namespace.lookupGlobal, found]

theorem Namespace.builtin_fallback (space : Namespace) {name : String}
    (absent : lookupBinding space.moduleGlobals name = none) :
    space.lookupGlobal name = lookupBinding space.builtins name := by
  simp [Namespace.lookupGlobal, absent]

theorem Namespace.bind_preserves_builtins (space : Namespace) (name : String) (value : Value) :
    (space.bindGlobal name value).builtins = space.builtins := rfl

theorem Operand.eval_local {slots : Nat} (space : Namespace) (locals : Locals slots) (slot : Fin slots) :
    (Operand.local slot).eval space locals =
      (locals.get slot).elim (.error (.raised (.runtime (.unboundLocal slot.val)))) .ok := rfl

theorem Expectation.delivers_iff {expectation : Expectation} {input output : Result} :
    expectation.deliver input = output ↔ Delivers expectation input output :=
  Proofs.Languages.Python.Core.Module.SeededCall.delivers_iff

theorem invoke_iff {callee : Value} {arguments : List Value} {result : Result} :
    invoke callee arguments = result ↔ Executes (Request.decode callee arguments) result :=
  Proofs.Languages.Python.Core.Module.SeededCall.invoke_iff

end Silmaril.Languages.Python.Core.Module.SeededCall
