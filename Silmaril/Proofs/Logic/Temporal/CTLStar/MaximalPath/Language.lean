module

public import Silmaril.Logic.Temporal.CTLStar.MaximalPath.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.MaximalPath
open Buchi.Automaton

/-- Every actual maximal path has either a finite endpoint or no endpoint.
The case split chooses a lifetime, without splitting one formula's operands. -/
theorem accepts_iff {A W : Type} (p : NNF.Formula A) (R : W → W → Prop)
    (label : W → A → Prop) (w : W) :
    AcceptsPath p R label w ↔ ∃ path : CTLStar.Path R, path.state 0 = w ∧
      p.Holds path.last (fun t => label (path.state t)) 0 := by
  rw [AcceptsPath, FiniteScalar.accepts_iff_ctlstarPath,
    InfiniteBridge.accepts_iff_ctlstarPath]
  constructor
  · rintro (⟨n, path, _, h0, hp⟩ | ⟨path, _, h0, hp⟩)
    · exact ⟨path, h0, hp⟩
    · exact ⟨path, h0, hp⟩
  · rintro ⟨path, h0, hp⟩
    cases hl : path.last with
    | none => exact Or.inr ⟨path, hl, h0, hp⟩
    | some n => exact Or.inl ⟨n, path, hl, h0, hp⟩

/-- Scalar denotation equals the independent finite-or-infinite run language. -/
theorem formula_iff_accepts {S : ModalMu.Signature} (p : NNF.Formula S.Atom)
    (a : S.Action) (M : ModalMu.Model S) (ρ : ModalMu.Env M.World 0) (w : M.World) :
    w ∈ (formula p a).denote M ρ ↔ AcceptsPath p (M.step a) (modelLabel M) w := by
  change (w ∈ (FiniteScalar.formula p a).denote M ρ ∨
    w ∈ (InfiniteBridge.formula p a).denote M ρ) ↔ _
  rw [FiniteScalar.formula, FiniteAutomaton.formula_correct,
    InfiniteBridge.formula, LTL.Tableau.formula, Generalized.formula_correct]
  rfl

/-- One maximal original graph path, retaining every formula constraint. -/
theorem formula_correct {S : ModalMu.Signature} (p : NNF.Formula S.Atom)
    (a : S.Action) (M : ModalMu.Model S) (ρ : ModalMu.Env M.World 0) (w : M.World) :
    w ∈ (formula p a).denote M ρ ↔ ∃ path : CTLStar.Path (M.step a),
      path.state 0 = w ∧ p.Holds path.last (fun t => modelLabel M (path.state t)) 0 := by
  rw [formula_iff_accepts, accepts_iff]

/-- Existing CTLStar existential path semantics with interpreted state leaves.
This interprets the leaves; it does not recursively compile them. -/
theorem accepts_iff_existsPath {A : Type} {S : CTLStar.Signature}
    (leaf : A → StateFormula S) (M : CTLStar.Model S) (p : NNF.Formula A)
    (w : M.toModal.World) :
    AcceptsPath p M.toModal.accessible (fun v a => (leaf a).Holds M v) w ↔
      (StateFormula.existsPath (p.toPathFormula leaf)).Holds M w := by
  rw [accepts_iff]
  exact exists_congr fun path => and_congr_right fun _ =>
    p.holds_toPathFormula leaf M path 0 path.valid_zero

/-- Both normalization polarities remain inside one chosen path's semantics. -/
theorem accepts_normalize_iff {S : CTLStar.Signature} (M : CTLStar.Model S)
    (p : PathFormula S) (b : Bool) (w : M.toModal.World) :
    AcceptsPath (NNF.normalize b p) M.toModal.accessible (fun v a => a.Holds M v) w ↔
      ∃ path : CTLStar.Path M.toModal.accessible, path.state 0 = w ∧
        (if b then ¬ p.Holds M path 0 else p.Holds M path 0) := by
  rw [accepts_iff]
  exact exists_congr fun path => and_congr_right fun _ =>
    NNF.normalize_holds M path p b 0 path.valid_zero

end Silmaril.Logic.Temporal.CTLStar.MaximalPath
