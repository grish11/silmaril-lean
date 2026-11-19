module
public import Silmaril.Elf.Corpus.SqliteGlobalVersion.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.SqliteGlobalVersion.Defs
public import Silmaril.Cerberus.Core.Outcome.Defs
public import Silmaril.Cerberus.Core.CallReach.Defs
/-! Actual initializer execution for a bounded post-startup candidate context.
This computation is not an initializer correctness theorem or a registered
contextual obligation. Failure remains an error, with no default memory/body. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteGlobalVersion.Initialization
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
abbrev Payload := Fin 64 → BitVec 8
def unrelatedAddress : Nat := 2097152
def initialMemory (payload : Payload) : Mem.Concrete.State :=
  {nextId := 1, lastAddress := globalAddress + 7,
   allocations := Map.ofList [(0, ⟨unrelatedAddress, 64, false, false, none, none, .UB064_modifying_const⟩)],
   bytes := Map.ofList ((List.finRange 64).map fun j =>
     (((unrelatedAddress+j.val : Nat) : Int), some ((payload j).toNat : Int)))}
/-- Execute the actual saved global initializer, retaining its allocations,
readonly/provenance metadata and bookkeeping, then enter the actual getter.
The fuel bounds this preparation computation; no termination/refinement law is
assumed for the eventual contextual problem. -/
def prepare (payload : Payload) : Except String State := do
  let (global, type, initializer, body) :=
    Source.Elaboration.actual.get Source.Elaboration.actual_exists
  let layout ← (Mem.Concrete.typeLayout 64 Source.Elaboration.core.toFile.tagDefs type).mapError
    (fun _ => "actual global layout unsupported")
  unless layout.size == 7 && layout.align == 1 do throw "actual char array layout mismatch"
  let initialized := run Source.Elaboration.core.toFile ∅ 2000
    ⟨.effectExpr initializer ∅, [], initialMemory payload⟩
  let some (.defined (.object (.pointer pointer@(.allocated id address)))) := initialized.ending
    | throw "actual global initializer did not return allocated object pointer"
  unless id == 1 && address == globalAddress do throw "actual initializer allocation placement mismatch"
  let env := extendEnv [(global, .object (.pointer pointer))] ∅
  return ⟨.effectExpr body env, [.procedureReturn (CallReach.bodyLabels body)], initialized.finalState.memory⟩
end Silmaril.Elf.Corpus.SqliteGlobalVersion.Initialization
