module

public import Silmaril.Proofs.Wasm.Logic.Reachability.WasmExpr.Compiler

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Reachability.WasmExpr
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- Exact native runs reach the same predicates as finite reachability. -/
theorem reaches_iff_steps {H : Type} (P : Profile) (host : HostSemantics H)
    (Q : Config H → Prop) (c : Config H) :
    Reaches (Step P host) Q c ↔ ∃ d, Steps P host c d ∧ Q d :=
  reaches_iff_reflTransGen

/-- Exact correspondence for arbitrary postconditions in the native-step model.
This includes both preservation and reflection of finite execution. -/
theorem compiled_iff_steps {H : Type} (P : Profile) (host : HostSemantics H)
    (initial : Config H) (Q : Config H → Prop) :
    Matching.FixedPoint.Sentence.Satisfies (predicateModel P host initial Q)
      (encode () (atomRule .finite false true)) ↔
        ∃ d, Steps P host initial d ∧ Q d := by
  let _ : Nonempty (Config H) := ⟨initial⟩
  rw [encode_correct]
  change (atomRule .finite false true).Satisfies ()
    (relationalModel (Step P host) (fun flag : Bool => {c | if flag then Q c else c = initial})) ↔ _
  rw [atomRule_iff]
  change (∀ c, c = initial → Reaches (Step P host) Q c) ↔ _
  constructor
  · intro h
    exact (reaches_iff_steps P host Q initial).mp (h initial rfl)
  · intro h c hc
    exact hc ▸ (reaches_iff_steps P host Q initial).mpr h

/-- An impossible target cannot become true through the matching compiler. -/
theorem compiled_false {H : Type} (P : Profile) (host : HostSemantics H)
    (initial : Config H) :
    ¬ Matching.FixedPoint.Sentence.Satisfies (predicateModel P host initial (fun _ => False))
      (encode () (atomRule .finite false true)) := by
  intro h
  obtain ⟨_, _, impossible⟩ := (compiled_iff_steps P host initial _).mp h
  exact impossible

/-- Existing interpreter soundness turns open-term evaluation into an actual
native Core execution, preserving the complete store, frame and older stack. -/
theorem executes {H : Type} {k : Nat} (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (rs : List Val) (locals : Fin k → LocalIdx)
    (values : Fin k → BitVec 32) (t : Expr k) (rest : List Admin)
    (agree : LocalsAgree f locals values) :
    Steps P host (start s f rs locals t rest) (finish s f rs values t rest) := by
  simpa only [start, finish] using
    (Silmaril.Wasm.Logic.Core.exec_sound (P := P) (host := host) rest
      (exec_code locals values t s f agree rs))

theorem reaches_result {H : Type} {k : Nat} (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (rs : List Val) (locals : Fin k → LocalIdx)
    (values : Fin k → BitVec 32) (t : Expr k) (rest : List Admin)
    (agree : LocalsAgree f locals values) :
    Reaches (Step P host) (fun c => c = finish s f rs values t rest) (start s f rs locals t rest) :=
  (reaches_iff_steps P host _ _).mpr ⟨_, executes P host s f rs locals values t rest agree, rfl⟩

/-- Finite reachability in the model using the actual native step relation. -/
theorem rule_valid {H : Type} {k : Nat} (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (rs : List Val) (locals : Fin k → LocalIdx)
    (values : Fin k → BitVec 32) (t : Expr k) (rest : List Admin)
    (agree : LocalsAgree f locals values) :
    (atomRule .finite false true).Satisfies ()
      (model P host (start s f rs locals t rest) (finish s f rs values t rest)) := by
  let _ : Nonempty (Config H) := ⟨finish s f rs values t rest⟩
  apply (atomRule_iff _ _ _ _ _).mpr
  intro c hc
  change c = start s f rs locals t rest at hc
  exact hc ▸ reaches_result P host s f rs locals values t rest agree

/-- Open-expression source evaluation reaches the native μ-matching sentence. -/
theorem compiled_valid {H : Type} {k : Nat} (P : Profile) (host : HostSemantics H)
    (s : Store H) (f : Frame) (rs : List Val) (locals : Fin k → LocalIdx)
    (values : Fin k → BitVec 32) (t : Expr k) (rest : List Admin)
    (agree : LocalsAgree f locals values) :
    Matching.FixedPoint.Sentence.Satisfies
      (model P host (start s f rs locals t rest) (finish s f rs values t rest))
      (encode () (atomRule .finite false true)) :=
  (encode_correct _ _).mpr (rule_valid P host s f rs locals values t rest agree)

end Silmaril.Logic.Reachability.WasmExpr
