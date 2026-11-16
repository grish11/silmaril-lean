module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Compiler.Defs

/-! Compilation of the already checked value-cell update profile. The emitted
assignment writes the same local read by the guard. -/
@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Logic.Kore.Operational.Conditional.WasmBranch

def rules (L : Layout) (z n : Int) : List Rule :=
  [⟨L.entry, L.zero, .zero, .val, z⟩, ⟨L.entry, L.nonzero, .nonzero, .val, n⟩]

def afterSource (L : Layout) (tail : List String) (q k : BitVec 32) (z n : Int) : Config :=
  ⟨L.name (selected q) :: tail, if q = 0 then z else n, k.toInt⟩

structure Compiled (p : CheckedProgram) (valueLocal : LocalIdx)
    (tailCode : List String → List Admin) extends Compiler.Plan valueLocal tailCode where
  installed : p.axioms = rules layout zeroLiteral nonzeroLiteral

/-- The original axiom list, including cell targets, is checked after shared
code generation. Claims are not installed as axioms. -/
def compile (p : CheckedProgram) (valueLocal : LocalIdx)
    (tailCode : List String → List Admin) : Option (Compiled p valueLocal tailCode) := do
  let result ← Compiler.planFor .val p.axioms valueLocal tailCode
  if installed : p.axioms = rules result.layout result.zeroLiteral result.nonzeroLiteral then
    some { result with installed := installed }
  else none

def compileText (input : String) (valueLocal : LocalIdx)
    (tailCode : List String → List Admin) :
    Option ((p : CheckedProgram) × Compiled p valueLocal tailCode) := do
  let p ← check input
  let c ← compile p valueLocal tailCode
  pure ⟨p, c⟩

/-- Records the exact source successor and actual native configuration. All
frame fields except the value local are retained by the explicit setLocal. -/
def postRelated {H : Type} (L : Layout) (s : Store H) (f : Frame)
    (older : List Val) (tail : List String) (rest : List Admin)
    (valueLocal counterLocal : LocalIdx) (q k : BitVec 32) (z n : Int)
    (d : Config) (w : Core.Config H) : Prop :=
  let updated := if q = 0 then z else n
  d = afterSource L tail q k z n ∧
  w = ⟨s, f.setLocal valueLocal (Val.i32 (BitVec.ofInt 32 updated)),
    vals older ++ L.tailCode tail ++ rest⟩ ∧
  LocalsAgree (f.setLocal valueLocal (Val.i32 (BitVec.ofInt 32 updated)))
    valueLocal counterLocal (BitVec.ofInt 32 updated) k ∧
  (BitVec.ofInt 32 updated).toInt = updated

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.ValueCompiler
