module

public import Silmaril.Proofs.Logic.ModalMu.K

@[expose] public section
namespace Silmaril.Logic.ModalMu
open Silmaril.Logic.Institution

/-- The modal inclusion preserves and reflects satisfiability. -/
theorem k_sat_iff {S : Modal.Signature} (p : Modal.Formula S) :
    (∃ M : Modal.Model S, Modal.Sat M p) ↔
      ∃ M : Model (kSignatures.obj S), Sat M (encodeK false p) := by
  constructor
  · rintro ⟨M, hp⟩
    exact ⟨expandK M, (expandK_sat M p).mpr hp⟩
  · rintro ⟨M, hp⟩
    exact ⟨forgetK M, (encodeK_holds M p M.point false).mp hp⟩

theorem k_unsat_iff {S : Modal.Signature} (p : Modal.Formula S) :
    (¬ ∃ M : Modal.Model S, Modal.Sat M p) ↔
      ¬ ∃ M : Model (kSignatures.obj S), Sat M (encodeK false p) :=
  not_congr (k_sat_iff p)

theorem k_entails_iff (S : Modal.Signature) (H : Set (Modal.Formula S))
    (p : Modal.Formula S) :
    (Modal.institution.obj S).Entails H p ↔
      (institution.obj (kSignatures.obj S)).Entails
        (encodeK false '' H) (encodeK false p) :=
  kToMu.entails_iff kToMu_modelExpansive S H p

/-- info: 'Silmaril.Logic.ModalMu.k_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms k_entails_iff

end Silmaril.Logic.ModalMu
