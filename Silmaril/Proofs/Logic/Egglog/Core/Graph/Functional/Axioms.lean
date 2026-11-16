module

public import Silmaril.Proofs.Logic.Egglog.Core.Graph.Functional.Universal

@[expose] public section
namespace Silmaril.Logic.Egglog.Core.Graph.Functional
open Silmaril.Logic.Institution.Examples

/-- The syntactic dependency axiom says exactly at-most-one output. -/
theorem fdSentence_holds {S : Signature} {n w s} (f : S.Function n w s)
    (M : FOL.Structure (signature S)) :
    (fdSentence f).Holds M ↔
      ∀ (args : ∀ i, M.carrier (w i)) (x y : M.carrier s),
        M.rel (.row (w := Fin.cases s w) f) (Fin.cases x args) →
        M.rel (.row (w := Fin.cases s w) f) (Fin.cases y args) → x = y := by
  rw [fdSentence, EQtoFOL.holds_closeAll]
  have eval_row (ρ : ∀ i, M.carrier (fdContext w s i))
      (t : EQ.Term S.toSignature (fdContext w s) s) :
      (fun j => EQ.Term.eval M.toAlgebra ρ
        (Fin.cases (motive := fun j => EQ.Term S.toSignature (fdContext w s) (Fin.cases (motive := fun _ => S.S) s w j)) t (fun i => .var i.succ.succ) j)) =
        Fin.cases (motive := fun j => M.carrier (Fin.cases (motive := fun _ => S.S) s w j))
          (EQ.Term.eval M.toAlgebra ρ t) (fun i => ρ i.succ.succ) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  constructor
  · intro h args x y hx hy
    have result := h (Fin.cases x (Fin.cases y args))
    simp only [fdFormula, FOL.Formula.Holds] at result
    rw [eval_row _ (.var 0), eval_row _ (.var 1)] at result
    simp only [EQ.Term.eval, fdContext, Fin.cases_zero, Fin.cases_succ,
      not_and, not_not] at result
    exact result ⟨hx, hy⟩
  · intro h ρ
    simp only [fdFormula, FOL.Formula.Holds]
    rw [eval_row _ (.var 0), eval_row _ (.var 1)]
    simpa only [EQ.Term.eval, fdContext, Fin.cases_zero, Fin.cases_succ,
      not_and, not_not] using
      (fun hh => h (fun i => ρ i.succ.succ) (ρ 0) (ρ 1) hh.1 hh.2)

private theorem row_eta {S : Signature} {n : Nat} {w : Fin (n+1) → S.S}
    (M : FOL.Structure (signature S)) (f : S.Function n (w ∘ Fin.succ) (w 0))
    (args : ∀ i : Fin n, M.carrier (w i.succ)) (x : M.carrier (w 0)) :
    M.rel (Relation.row (w := Fin.cases (w 0) (w ∘ Fin.succ)) f) (Fin.cases x args) =
      M.rel (Relation.row (w := w) f) (Fin.cases x args) := by
  have hw : Fin.cases (w 0) (w ∘ Fin.succ) = w := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  congr 1
  · have hh : ∀ (v : Fin (n+1) → S.S) (e : Fin.cases (w 0) (w ∘ Fin.succ) = v)
        (g : S.Function n (v ∘ Fin.succ) (v 0)), HEq f g →
        HEq (Relation.row (w := Fin.cases (w 0) (w ∘ Fin.succ)) f)
          (Relation.row (w := v) g) := by
      intro v e g hg
      cases e
      cases hg
      rfl
    exact hh w hw f HEq.rfl
  · apply Function.hfunext rfl
    intro i j hij
    cases hij
    exact Fin.cases HEq.rfl (fun _ => HEq.rfl) i

theorem fdTheory_holds_iff {S : Signature} (M : FOL.Structure (signature S)) :
    (∀ p ∈ fdTheory S, p.Holds M) ↔ FD S M := by
  constructor
  · intro h n w f
    have hh := (fdSentence_holds f M).mp (h _ ⟨n,w ∘ Fin.succ,w 0,f,rfl⟩)
    intro args x y hx hy
    exact hh args x y (Eq.mpr (row_eta M f args x) hx) (Eq.mpr (row_eta M f args y) hy)
  · intro h p hp
    obtain ⟨n,w,s,f,rfl⟩ := hp
    apply (fdSentence_holds f M).mpr
    have hh := @h n (Fin.cases s w)
    simp only [Function.comp_def, Fin.cases_zero, Fin.cases_succ] at hh
    exact hh f

/-- Independent ordinary FOL models of the explicit FD theory reconstruct exactly
all old graph models, for arbitrary additional full FOL theories. -/
theorem relative_sat_iff {S : Signature} (H : Set (FOL.Sentence (signature S))) :
    (∃ M : FOL.Structure (signature S), ∀ p ∈ fdTheory S ∪ H, p.Holds M) ↔
      ∃ M : Core.Model S, ∀ p ∈ H, p.Holds (model M) := by
  rw [← sat_iff H]
  constructor
  · rintro ⟨M,h⟩
    exact ⟨⟨M,(fdTheory_holds_iff M).mp (fun p hp => h p (Or.inl hp))⟩,
      fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨M,h⟩
    refine ⟨M.obj,?_⟩
    intro p hp
    rcases hp with hp | hp
    · exact (fdTheory_holds_iff M.obj).mpr M.property p hp
    · exact h p hp

theorem relative_unsat_iff {S : Signature} (H : Set (FOL.Sentence (signature S))) :
    (¬ ∃ M : FOL.Structure (signature S), ∀ p ∈ fdTheory S ∪ H, p.Holds M) ↔
      ¬ ∃ M : Core.Model S, ∀ p ∈ H, p.Holds (model M) :=
  not_congr (relative_sat_iff H)

theorem relative_entails_iff {S : Signature} (H : Set (FOL.Sentence (signature S)))
    (p : FOL.Sentence (signature S)) :
    (∀ M : FOL.Structure (signature S),
      (∀ q ∈ fdTheory S ∪ H, q.Holds M) → p.Holds M) ↔
      ∀ M : Core.Model S, (∀ q ∈ H, q.Holds (model M)) → p.Holds (model M) := by
  rw [← entails_iff H p]
  constructor
  · intro h M hm
    apply h M.obj
    intro q hq
    rcases hq with hq | hq
    · exact (fdTheory_holds_iff M.obj).mpr M.property q hq
    · exact hm q hq
  · intro h M hm
    exact h ⟨M,(fdTheory_holds_iff M).mp (fun q hq => hm q (Or.inl hq))⟩
      (fun q hq => hm q (Or.inr hq))

/-- In particular the original normalized rules and queries retain exact SAT. -/
theorem normalized_relative_sat_iff {S : Signature} (H : Set (Core.Sentence S)) :
    (∃ M : FOL.Structure (signature S),
      ∀ p ∈ fdTheory S ∪ (Graph.sentence '' H), p.Holds M) ↔
      ∃ M : Core.Model S, ∀ s ∈ H, s.Holds M :=
  (relative_sat_iff (Graph.sentence '' H)).trans (Graph.sat_iff H).symm

/-- Consequence is borrowed using the genuine reconstruction expansion theorem. -/
theorem normalized_entails_iff (S : Signature) (H : Set (Core.Sentence S))
    (s : Core.Sentence S) :
    (Core.room S).Entails H s ↔
      (room S).Entails (Graph.sentence '' H) (Graph.sentence s) :=
  fromCore.entails_iff fromCore_modelExpansive S H s

end Silmaril.Logic.Egglog.Core.Graph.Functional
