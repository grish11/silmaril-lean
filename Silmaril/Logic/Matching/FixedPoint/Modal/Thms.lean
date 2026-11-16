module

public import Silmaril.Proofs.Logic.Matching.FixedPoint.Modal

@[expose] public section
namespace Silmaril.Logic.Matching.FixedPoint
variable {L : Silmaril.Logic.ModalMu.Signature}

theorem expandModal_satisfies (M : ModalMu.Model L) (p : ModalMu.Formula L 0) :
    (expandModal M).Satisfies (encodeModal p) ↔ ModalMu.Sat M p := by
  have h : (expandModal M).Satisfies (encodeModal p) ↔ ModalMu.Sat (forgetModal (expandModal M)) p :=
    Set.ext_iff.mp (congrArg (fun F => F (fun i => i.elim0))
      (encodeModal_denote (expandModal M) p)) M.point
  exact h.trans (by rw [forget_expandModal])

/-- Pointwise matching reachability is an actual finite path, on every target model. -/
theorem matching_reach_iff (M : PointedModel () (modalSignature L))
    (a : L.Action) (p : L.Atom) :
    M.Satisfies (encodeModal (ModalMu.reach a p)) ↔
      ModalMu.FiniteReach ((forgetModal M).step a) ((forgetModal M).valuation p) M.point := by
  change M.point ∈ (encodeModal (ModalMu.reach a p)).denote M.base _ _ ↔ _
  exact (Set.ext_iff.mp (congrArg (fun F => F (fun i => i.elim0))
    (encodeModal_denote M (ModalMu.reach a p))) M.point).trans
      (ModalMu.reach_iff (forgetModal M) a p M.point)

/-- A closed translated formula is globally valid exactly when true at every point. -/
theorem global_modal_iff (M : Model (modalSignature L)) (p : ModalMu.Formula L 0) :
    Sentence.Satisfies M (closedSentence (encodeModal p)) ↔
      ∀ point : M.carrier (), ModalMu.Sat (forgetModal ⟨M, point⟩) p := by
  rw [global_iff_all_points]
  apply forall_congr'
  intro point
  exact Set.ext_iff.mp (congrArg (fun F => F (fun i => i.elim0))
    (encodeModal_denote ⟨M, point⟩ p)) point

end Silmaril.Logic.Matching.FixedPoint
