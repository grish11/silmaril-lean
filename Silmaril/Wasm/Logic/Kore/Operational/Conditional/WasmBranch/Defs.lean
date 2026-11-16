module

public import Silmaril.Logic.Kore.Operational.Conditional.Thms
public import Silmaril.Wasm.Logic.Reachability.WasmExpr.Thms
public import Silmaril.Wasm.Execution.Core.Properties

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.WasmBranch
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core

/-- Distinct source state names, with zero mapped to Wasm's else branch. -/
structure Layout where
  entry : String
  zero : String
  nonzero : String
  entry_ne_zero : entry ≠ zero
  entry_ne_nonzero : entry ≠ nonzero
  zero_ne_nonzero : zero ≠ nonzero
  blockType : BlockType
  zeroBody : List Instr
  nonzeroBody : List Instr
  tailCode : List String → List Admin

inductive Phase | entry | zero | nonzero deriving DecidableEq

def Layout.name (L : Layout) : Phase → String
  | .entry => L.entry
  | .zero => L.zero
  | .nonzero => L.nonzero

def Layout.rules (L : Layout) : List Rule :=
  [⟨L.entry, L.zero, .zero⟩, ⟨L.entry, L.nonzero, .nonzero⟩]

def selected (q : BitVec 32) : Phase := if q = 0 then .zero else .nonzero

def source (L : Layout) (phase : Phase) (tail : List String) (q k : BitVec 32) :
    Conditional.Config := ⟨L.name phase :: tail, q.toInt, k.toInt⟩

/-- Both values are observed in actual initialized locals. Shared local indices
are allowed exactly when the two lookup requirements are compatible. -/
def LocalsAgree (f : Frame) (valueLocal counterLocal : LocalIdx) (q k : BitVec 32) : Prop :=
  Silmaril.Wasm.Logic.Core.localVal? f valueLocal = some (Val.i32 q) ∧
    Silmaril.Wasm.Logic.Core.localVal? f counterLocal = some (Val.i32 k)

def native {H : Type} (L : Layout) (phase : Phase) (s : Store H) (f : Frame)
    (older : List Val) (tail : List String) (rest : List Admin) (valueLocal : LocalIdx) :
    Core.Config H :=
  ⟨s, f, vals older ++
    (match phase with
    | .entry => [.plain (.localGet valueLocal), .plain (.if_ L.blockType L.nonzeroBody L.zeroBody)]
    | .zero => [.plain (.block L.blockType L.zeroBody)]
    | .nonzero => [.plain (.block L.blockType L.nonzeroBody)]) ++ L.tailCode tail ++ rest⟩

/-- Explicit source/native relation; the complete tail, signed value/counter,
store/frame, older operands and administrative continuation are retained. -/
def Related {H : Type} (L : Layout) (phase : Phase) (s : Store H) (f : Frame)
    (older : List Val) (tail : List String) (rest : List Admin)
    (valueLocal counterLocal : LocalIdx) (q k : BitVec 32)
    (c : Conditional.Config) (w : Core.Config H) : Prop :=
  c = source L phase tail q k ∧ w = native L phase s f older tail rest valueLocal ∧
    LocalsAgree f valueLocal counterLocal q k

end Silmaril.Logic.Kore.Operational.Conditional.WasmBranch
