module

public import Silmaril.Logic.Consequence.Gentzen.Clausal.Thms
public import Silmaril.Logic.Consequence.Gentzen.Calculus.Examples

/-!
# Examples: clausal acceptors, their closure laws and equivalences

Over the literals of `Gentzen.Examples` (`Lit := Bool × Nat`, `lsat`, the exact negation
`lneg`):

* the complementary-pair test `pairs` is the UNSAT restriction of literal validity, hence
  `UnsatClosed` (`pairs_unsatClosed`); its CNF acceptor is CNF unsatisfiability
  (`cnfOf_pairs`), and the equivalences send validity to `pairs` and back
  (`unsatEquiv_valid`, `unsatEquiv_symm_pairs`, `gentzenCnfEquiv_valid`);
* a CNF refutation by the closure laws alone: `(p ∨ q) ∧ ¬p ∧ ¬q` (`threeClauses_unsat`);
* the two CNF layers differ: "contains the empty clause" (`emptyClause`) is sound and
  `CnfClosed`, but not `CnfUnsatClosed` (`emptyClause_not_unsatClosed`): its unit restriction
  accepts nothing (`unitsOf_emptyClause`);
* the bounded test `bounded 3` is sound but not up-closed, so it is not the restriction of any
  `GentzenClosed` calculus (`bounded_not_unsatClosed`).

Over signed atoms, the identity calculus on `ℕ` becomes the complementary-pair test on signed
lists (`signedUnsat_identity_iff`), and it is recovered from it (`identity_roundtrip`).
-/

@[expose] public section

namespace Silmaril.Consequence.Gentzen.Clausal.Examples

open Gentzen.Examples

/-! ## Literal validity, `pairs`, and the equivalences -/

theorem valid_gentzenClosed : GentzenClosed lneg (Valid lsat) :=
  ⟨valid_closed, valid_negL lneg_sound, valid_negR lneg_complete⟩

theorem toUnsat_valid_eq_pairs : toUnsat (Valid lsat) = pairs := by
  rw [← viaUnsat_pairs_eq, toUnsat_viaUnsat]

theorem pairs_unsatClosed : UnsatClosed lneg pairs :=
  toUnsat_valid_eq_pairs ▸ unsatClosed_toUnsat valid_gentzenClosed

theorem cnfOf_pairs : cnfOf pairs = CnfUnsat lsat := by
  rw [← toUnsat_valid_eq_pairs, cnfOf_toUnsat_valid]

theorem unsatEquiv_valid : (unsatEquiv lneg ⟨Valid lsat, valid_gentzenClosed⟩).1 = pairs :=
  toUnsat_valid_eq_pairs

theorem unsatEquiv_symm_pairs : ((unsatEquiv lneg).symm ⟨pairs, pairs_unsatClosed⟩).1 = Valid lsat :=
  viaUnsat_pairs_eq

theorem gentzenCnfEquiv_valid :
    (gentzenCnfEquiv lneg ⟨Valid lsat, valid_gentzenClosed⟩).1 = CnfUnsat lsat :=
  cnfOf_toUnsat_valid

/-- The TAUTO restriction of validity has excluded middle by its closure law. -/
example : toTaut (Valid lsat) [(true, 0), (false, 0)] :=
  (tautClosed_toTaut valid_gentzenClosed).excluded (c := (true, 0)) (by decide) (by decide)

/-- The CNF and UNSAT acceptors agree on units, in both directions. -/
example : unitsOf (cnfOf pairs) [(true, 0), (false, 0)] := by
  rw [unitsOf_cnfOf pairs_unsatClosed.up]; decide

/-! ## A refutation by the closure laws -/

/-- `(p ∨ q) ∧ ¬p ∧ ¬q`. -/
def threeClauses : List (List Lit) := [[(true, 0), (true, 1)], [(false, 0)], [(false, 1)]]

/-- Split the first clause; each branch contains complementary units. -/
theorem threeClauses_unsat : CnfUnsat lsat threeClauses := by
  have h := cnfUnsat_unsatClosed (sat := lsat) lneg_sound lneg_complete
  refine h.split ?_ ?_
  · exact h.up _ _ (by decide) (h.complement (true, 0))
  · exact h.up _ _ (by decide) (h.complement (true, 1))

/-! ## Representation closure is not logical closure -/

/-- Accept exactly the formulas containing the empty clause. -/
def emptyClause (F : List (List Lit)) : Prop := [] ∈ F

theorem emptyClause_cnfClosed : CnfClosed emptyClause := by
  refine ⟨fun _ _ h hF => h hF, fun K K' F hK h => ?_, fun a K F h₁ _ => ?_, fun _ => ?_⟩
  · rcases List.mem_cons.1 h with h | h
    · subst h
      rw [List.subset_nil.1 hK]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ h
  · rcases List.mem_cons.1 h₁ with h | h
    · exact absurd h (by simp)
    · exact List.mem_cons_of_mem _ h
  · exact List.mem_cons_self

theorem emptyClause_sound : CnfSound lsat emptyClause := fun F hF m hm => by
  obtain ⟨_, hc, _⟩ := hm [] hF
  exact absurd hc List.not_mem_nil

theorem unitsOf_emptyClause (Γ : List Lit) : ¬ unitsOf emptyClause Γ := fun h => by
  obtain ⟨c, _, hc⟩ := List.mem_map.1 h
  exact absurd hc (by simp)

theorem emptyClause_not_unsatClosed : ¬ CnfUnsatClosed lneg emptyClause := fun h =>
  absurd (h.complement (true, 0)) (by simp [emptyClause])

/-! ## A sound acceptor that is not closed -/

theorem bounded_not_up : ¬ ListPred.UpClosed (bounded 3) := fun h =>
  absurd (h [(true, 0), (false, 0)] [(true, 0), (false, 0), (true, 1), (true, 2)] (by decide)
    (by decide)) (by decide)

theorem bounded_not_unsatClosed : ¬ UnsatClosed lneg (bounded 3) := fun h => bounded_not_up h.up

/-! ## Signed atoms -/

/-- The identity calculus on atoms. -/
abbrev identityA : Seq ℕ := Derives defaultRules ⊥

theorem signedUnsat_identity_iff (Γ : List (Signed ℕ)) :
    signedUnsat identityA Γ ↔ ∃ a, Signed.pos a ∈ Γ ∧ Signed.neg a ∈ Γ := by
  rw [signedUnsat_iff]
  exact identity_iff_overlap.trans (by simp [mem_posAtoms, mem_negAtoms])

example : signedUnsat identityA [.pos 0, .neg 0] :=
  (signedUnsat_identity_iff _).2 ⟨0, by simp, by simp⟩

example : ¬ signedUnsat identityA [.pos 0, .neg 1] := fun h => by
  obtain ⟨a, ha, hb⟩ := (signedUnsat_identity_iff _).1 h
  simp at ha hb
  omega

theorem identity_roundtrip :
    ((signedEquiv ℕ).symm (signedEquiv ℕ ⟨identityA, derives_closed _ _⟩)).1 = identityA :=
  atomSeq_signedUnsat identityA

end Silmaril.Consequence.Gentzen.Clausal.Examples
