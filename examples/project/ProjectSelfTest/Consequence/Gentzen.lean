module

public import Silmaril.Project.Shapes.Consequence.Thms
public import Silmaril.Logic.Consequence.Gentzen.Examples
public import Silmaril.Logic.Consequence.Gentzen.Calculus.Examples

/-!
# The `sil project` self-test: consequence systems from `Silmaril.Logic.Consequence.Gentzen`

The literal sequents of `Silmaril.Consequence.Gentzen.Examples` (literals `Bool × Nat`, a
sequent `Γ ⊢ Δ` between lists, valid when every assignment satisfying all of `Γ` satisfies some
literal of `Δ`), registered as consequence systems, with the library's own theorems as answers:

* `valid` (the semantics `Valid lsat`) and `via_unsat_pairs` (the complementary-pair test
  applied to `Γ, ¬Δ`): equal, so each is sound and complete for the other;
* `via_unsat_bounded3` (the same test, only on at most three literals) and its closure under the
  default Gentzen rules `bounded3_closure`: both sound for `valid`; the raw relation is not
  closed under cut, so it is **not complete for its own closure** (the counterexample is the
  cut of `p, r ⊢ p` and `p, q ⊢ p`, kept as the witness);
* `chain` (the non-logical sequents `p ⊢ q`, `q ⊢ r`) and its closure: `p ⊢ r` holds in the
  closure (by cut) and not in the raw relation.

Here `p`, `q`, `r` are the positive literals `(true, 0)`, `(true, 1)`, `(true, 2)`.
-/

namespace ProjectSelfTest.Consequence.Gentzen

open Silmaril.Consequence.Gentzen Silmaril.Consequence.Gentzen.Examples

@[expose] public section

/-- Validity of literal sequents. -/
def valid : Seq Lit := Valid lsat
/-- The complementary-pair test on `Γ, ¬Δ`. -/
def viaUnsatPairs : Seq Lit := viaUnsat pairs lneg
/-- The test on at most three literals. -/
def viaUnsatBounded3 : Seq Lit := viaUnsat (bounded 3) lneg
/-- Its closure under reflexivity, the default weakening and cut. -/
def bounded3Closure : Seq Lit := Derives defaultRules (viaUnsat (bounded 3) lneg)
/-- Validity rebuilt from its UNSAT restriction: `viaUnsat (toUnsat valid) lneg`. -/
def validViaUnsatRestriction : Seq Lit := viaUnsat (toUnsat (Valid lsat)) lneg

/-- Validity rebuilt from its TAUTO restriction: `viaTauto (toTaut valid) lneg`. -/
def validViaTautRestriction : Seq Lit := viaTauto (toTaut (Valid lsat)) lneg

/-- The pure identity calculus over literals (`Calculus.Examples.identity`). -/
def identityLit : Seq Lit := Calculus.Examples.identity

/-- The identity calculus rebuilt from its UNSAT restriction. -/
def identityViaUnsat : Seq Lit := viaUnsat (toUnsat Calculus.Examples.identity) lneg

/-- The non-logical sequents `p ⊢ q` and `q ⊢ r`. -/
def chainRaw : Seq Lit := chain
/-- Their closure under the default rules. -/
def chainClosure : Seq Lit := Derives defaultRules chain

end

end ProjectSelfTest.Consequence.Gentzen

/-! ## Systems -/

silmaril consequence_system silmaril.selftest.consequence.gentzen.valid :=
  ProjectSelfTest.Consequence.Gentzen.valid (title := "Valid literal sequents")
silmaril consequence_system silmaril.selftest.consequence.gentzen.via_unsat_pairs :=
  ProjectSelfTest.Consequence.Gentzen.viaUnsatPairs
  (title := "The complementary-pair UNSAT test on Γ, ¬Δ")
silmaril consequence_system silmaril.selftest.consequence.gentzen.via_unsat_bounded3 :=
  ProjectSelfTest.Consequence.Gentzen.viaUnsatBounded3
  (title := "The pair test on at most three literals (raw, not cut-closed)")
silmaril consequence_system silmaril.selftest.consequence.gentzen.bounded3_closure :=
  ProjectSelfTest.Consequence.Gentzen.bounded3Closure
  (title := "The bounded test closed under reflexivity, weakening and cut")
silmaril consequence_system silmaril.selftest.consequence.gentzen.valid_via_unsat_restriction :=
  ProjectSelfTest.Consequence.Gentzen.validViaUnsatRestriction
  (title := "Validity rebuilt from its UNSAT restriction toUnsat (Calculus)")
silmaril consequence_system silmaril.selftest.consequence.gentzen.valid_via_taut_restriction :=
  ProjectSelfTest.Consequence.Gentzen.validViaTautRestriction
  (title := "Validity rebuilt from its TAUTO restriction toTaut (Calculus)")
silmaril consequence_system silmaril.selftest.consequence.gentzen.identity :=
  ProjectSelfTest.Consequence.Gentzen.identityLit
  (title := "The identity calculus over literals (Derives defaultRules ⊥)")
silmaril consequence_system silmaril.selftest.consequence.gentzen.identity_via_unsat :=
  ProjectSelfTest.Consequence.Gentzen.identityViaUnsat
  (title := "The identity calculus rebuilt from its UNSAT restriction (no negation rules: not equal)")
silmaril consequence_system silmaril.selftest.consequence.gentzen.chain :=
  ProjectSelfTest.Consequence.Gentzen.chainRaw (title := "Non-logical sequents p ⊢ q, q ⊢ r (raw)")
silmaril consequence_system silmaril.selftest.consequence.gentzen.chain_closure :=
  ProjectSelfTest.Consequence.Gentzen.chainClosure
  (title := "p ⊢ q, q ⊢ r closed under the default Gentzen rules")

/-! ## Problems -/

open ProjectSelfTest.Consequence.Gentzen Silmaril.Consequence.Gentzen
  Silmaril.Consequence.Gentzen.Examples Silmaril.Project.Shapes.Consequence in
section

silmaril instance silmaril.selftest.consequence.gentzen.pairs_sound (expect := THM)
  (title := "The pair test is sound for validity") := silmaril.shapes.consequence.sound_at
  (S := ProjectSelfTest.Consequence.Gentzen.viaUnsatPairs) (T := ProjectSelfTest.Consequence.Gentzen.valid)

@[answers "silmaril.selftest.consequence.gentzen.pairs_sound" thm]
public theorem pairs_sound_at : ∀ Γ Δ, SoundAt viaUnsatPairs valid Γ Δ :=
  fun Γ Δ h => (viaUnsat_pairs_eq ▸ h : Valid lsat Γ Δ)

silmaril instance silmaril.selftest.consequence.gentzen.pairs_complete (expect := THM)
  (title := "The pair test is complete for validity") := silmaril.shapes.consequence.complete_at
  (S := ProjectSelfTest.Consequence.Gentzen.viaUnsatPairs) (T := ProjectSelfTest.Consequence.Gentzen.valid)

@[answers "silmaril.selftest.consequence.gentzen.pairs_complete" thm]
public theorem pairs_complete_at : ∀ Γ Δ, CompleteAt viaUnsatPairs valid Γ Δ :=
  fun Γ Δ h => (viaUnsat_pairs_eq ▸ h : viaUnsat pairs lneg Γ Δ)

-- certified Gentzen closure: the pair test is closed under the default rules; the bounded test
-- is not (no cut)
silmaril instance silmaril.selftest.consequence.gentzen.pairs_closed (expect := THM)
  (title := "The pair test is closed under the default Gentzen rules (refl, ⊆-weakening, cut)") :=
  silmaril.shapes.consequence.gentzen_closed (rs := Silmaril.Consequence.Gentzen.defaultRules)
  (S := ProjectSelfTest.Consequence.Gentzen.viaUnsatPairs)

@[answers "silmaril.selftest.consequence.gentzen.pairs_closed" thm]
public theorem pairs_closed : GentzenClosed defaultRules viaUnsatPairs := viaUnsat_pairs_closed

silmaril instance silmaril.selftest.consequence.gentzen.bounded3_closed (expect := UNS)
  (title := "The bounded test is closed under the default Gentzen rules (fails: not cut-closed)") :=
  silmaril.shapes.consequence.gentzen_closed (rs := Silmaril.Consequence.Gentzen.defaultRules)
  (S := ProjectSelfTest.Consequence.Gentzen.viaUnsatBounded3)

@[answers "silmaril.selftest.consequence.gentzen.bounded3_closed" csa]
public theorem bounded3_closed : ¬ GentzenClosed defaultRules viaUnsatBounded3 :=
  fun h => bounded_not_cut (h.cut trivial)

-- shape evidence: the pair test's contexts may be weakened and are read as sets; the bounded test's may not
silmaril instance silmaril.selftest.consequence.gentzen.pairs_up_closed (expect := THM)
  (title := "The pair test: contexts may be weakened (⊆)") := silmaril.shapes.consequence.ctx_up_closed
  (S := ProjectSelfTest.Consequence.Gentzen.viaUnsatPairs)

theorem pairs_mono {X Y : List Lit} (h : X ⊆ Y) : pairs X → pairs Y :=
  fun ⟨l, hl, hn⟩ => ⟨l, h hl, h hn⟩

theorem append_subset_right {X Y M : List Lit} (h : X ⊆ Y) : X ++ M ⊆ Y ++ M := fun x hx => by
  simp only [List.mem_append] at hx ⊢; exact hx.imp_left (h ·)

@[answers "silmaril.selftest.consequence.gentzen.pairs_up_closed" thm]
public theorem pairs_up_closed : CtxUpClosed viaUnsatPairs :=
  fun _ _ _ s h => pairs_mono (append_subset_right s) h

silmaril instance silmaril.selftest.consequence.gentzen.pairs_set_inv (expect := THM)
  (title := "The pair test: contexts are read as sets") := silmaril.shapes.consequence.ctx_set_inv
  (S := ProjectSelfTest.Consequence.Gentzen.viaUnsatPairs)

@[answers "silmaril.selftest.consequence.gentzen.pairs_set_inv" thm]
public theorem pairs_set_inv : CtxSetInv viaUnsatPairs :=
  fun Δ l l' h => ⟨pairs_up_closed Δ l l' (fun x hx => (h x).1 hx), pairs_up_closed Δ l' l (fun x hx => (h x).2 hx)⟩

silmaril instance silmaril.selftest.consequence.gentzen.bounded3_up_closed (expect := UNS)
  (title := "The bounded test: contexts may be weakened (fails: p ⊢ p, but not p, q, r ⊢ p)") :=
  silmaril.shapes.consequence.ctx_up_closed (S := ProjectSelfTest.Consequence.Gentzen.viaUnsatBounded3)

@[answers "silmaril.selftest.consequence.gentzen.bounded3_up_closed" csa]
public theorem bounded3_up_closed : ¬ CtxUpClosed viaUnsatBounded3 := fun h =>
  absurd (h [(true, 0)] [(true, 0)] [(true, 0), (true, 1), (true, 2)] (by decide)
    (show viaUnsat (bounded 3) lneg [(true, 0)] [(true, 0)] by decide))
    (show ¬ viaUnsat (bounded 3) lneg [(true, 0), (true, 1), (true, 2)] [(true, 0)] by decide)

-- the UNSAT restriction loses nothing for validity (Calculus.Examples.lit_eq_viaUnsat)
silmaril instance silmaril.selftest.consequence.gentzen.restriction_sound (expect := THM)
  (title := "Validity rebuilt from toUnsat is sound for validity") := silmaril.shapes.consequence.sound_at
  (S := ProjectSelfTest.Consequence.Gentzen.validViaUnsatRestriction) (T := ProjectSelfTest.Consequence.Gentzen.valid)

@[answers "silmaril.selftest.consequence.gentzen.restriction_sound" thm]
public theorem restriction_sound : ∀ Γ Δ, SoundAt validViaUnsatRestriction valid Γ Δ := fun Γ Δ h =>
  (show Valid lsat Γ Δ from Calculus.Examples.lit_eq_viaUnsat ▸ h)

silmaril instance silmaril.selftest.consequence.gentzen.restriction_complete (expect := THM)
  (title := "…and complete: toUnsat loses nothing for validity") := silmaril.shapes.consequence.complete_at
  (S := ProjectSelfTest.Consequence.Gentzen.validViaUnsatRestriction) (T := ProjectSelfTest.Consequence.Gentzen.valid)

@[answers "silmaril.selftest.consequence.gentzen.restriction_complete" thm]
public theorem restriction_complete : ∀ Γ Δ, CompleteAt validViaUnsatRestriction valid Γ Δ := fun Γ Δ h =>
  (show viaUnsat (toUnsat (Valid lsat)) lneg Γ Δ from Calculus.Examples.lit_eq_viaUnsat ▸ h)

-- the TAUTO restriction too, under the stated hypotheses (closed under the default rules, NegL, NegR)
silmaril instance silmaril.selftest.consequence.gentzen.taut_restriction_sound (expect := THM)
  (title := "Validity rebuilt from toTaut is sound for validity (default rules, NegL and NegR from lneg_sound/lneg_complete)") :=
  silmaril.shapes.consequence.sound_at
  (S := ProjectSelfTest.Consequence.Gentzen.validViaTautRestriction) (T := ProjectSelfTest.Consequence.Gentzen.valid)

theorem valid_eq_viaTauto : Valid lsat = viaTauto (toTaut (Valid lsat)) lneg :=
  eq_viaTauto_toTaut valid_closed (valid_negL lneg_sound) (valid_negR lneg_complete)

@[answers "silmaril.selftest.consequence.gentzen.taut_restriction_sound" thm]
public theorem taut_restriction_sound : ∀ Γ Δ, SoundAt validViaTautRestriction valid Γ Δ := fun Γ Δ h =>
  (show Valid lsat Γ Δ from valid_eq_viaTauto ▸ h)

silmaril instance silmaril.selftest.consequence.gentzen.taut_restriction_complete (expect := THM)
  (title := "…and complete for validity") := silmaril.shapes.consequence.complete_at
  (S := ProjectSelfTest.Consequence.Gentzen.validViaTautRestriction) (T := ProjectSelfTest.Consequence.Gentzen.valid)

@[answers "silmaril.selftest.consequence.gentzen.taut_restriction_complete" thm]
public theorem taut_restriction_complete : ∀ Γ Δ, CompleteAt validViaTautRestriction valid Γ Δ := fun Γ Δ h =>
  (show viaTauto (toTaut (Valid lsat)) lneg Γ Δ from valid_eq_viaTauto ▸ h)

-- without negation rules the UNSAT restriction loses sequents: the identity calculus
silmaril instance silmaril.selftest.consequence.gentzen.identity_closed (expect := THM)
  (title := "The identity calculus is closed under the default Gentzen rules") :=
  silmaril.shapes.consequence.gentzen_closed (rs := Silmaril.Consequence.Gentzen.defaultRules)
  (S := ProjectSelfTest.Consequence.Gentzen.identityLit)

@[answers "silmaril.selftest.consequence.gentzen.identity_closed" thm]
public theorem identity_closed : GentzenClosed defaultRules identityLit := derives_closed defaultRules ⊥

silmaril instance silmaril.selftest.consequence.gentzen.identity_restriction_sound (expect := CSA)
  (title := "The identity calculus is sound for its UNSAT rebuild (fails: p ⊢ p, but not p, ¬p ⊢; no NegL)") :=
  silmaril.shapes.consequence.sound_at (S := ProjectSelfTest.Consequence.Gentzen.identityLit)
  (T := ProjectSelfTest.Consequence.Gentzen.identityViaUnsat)

@[answers "silmaril.selftest.consequence.gentzen.identity_restriction_sound" csa]
public theorem identity_restriction_sound : ∃ Γ Δ, ¬ SoundAt identityLit identityViaUnsat Γ Δ :=
  ⟨[(true, 0)], [(true, 0)], fun h => Calculus.Examples.identity_not_explosion
    (by simpa [identityViaUnsat, viaUnsat, toUnsat, lneg] using h Calculus.Examples.identity_p_p)⟩

silmaril instance silmaril.selftest.consequence.gentzen.p_qp (expect := THM)
  (title := "p ⊢ q, p is valid") := silmaril.shapes.consequence.derives
  (S := ProjectSelfTest.Consequence.Gentzen.valid) (Γ := [(true, 0)]) (φ := [(true, 1), (true, 0)])

@[answers "silmaril.selftest.consequence.gentzen.p_qp" thm]
public theorem p_qp : Derives valid [(true, 0)] [(true, 1), (true, 0)] :=
  show Valid lsat _ _ from viaUnsat_pairs_eq ▸ (by decide : viaUnsat pairs lneg [(true, 0)] [(true, 1), (true, 0)])

silmaril instance silmaril.selftest.consequence.gentzen.p_q (expect := UNS)
  (title := "p ⊢ q is valid (fails)") := silmaril.shapes.consequence.derives
  (S := ProjectSelfTest.Consequence.Gentzen.valid) (Γ := [(true, 0)]) (φ := [(true, 1)])

@[answers "silmaril.selftest.consequence.gentzen.p_q" csa]
public theorem p_q : ¬ Derives valid [(true, 0)] [(true, 1)] :=
  show ¬ Valid lsat _ _ from viaUnsat_pairs_eq ▸ (by decide : ¬ viaUnsat pairs lneg [(true, 0)] [(true, 1)])

silmaril instance silmaril.selftest.consequence.gentzen.bounded3_sound (expect := THM)
  (title := "The bounded test is sound for validity") := silmaril.shapes.consequence.sound_at
  (S := ProjectSelfTest.Consequence.Gentzen.viaUnsatBounded3) (T := ProjectSelfTest.Consequence.Gentzen.valid)

@[answers "silmaril.selftest.consequence.gentzen.bounded3_sound" thm]
public theorem bounded3_sound : ∀ Γ Δ, SoundAt viaUnsatBounded3 valid Γ Δ :=
  viaUnsat_le_valid (bounded_sound 3) lneg_complete

silmaril instance silmaril.selftest.consequence.gentzen.bounded3_closure_sound (expect := THM)
  (title := "The closure of the bounded test is sound for validity") :=
  silmaril.shapes.consequence.sound_at
  (S := ProjectSelfTest.Consequence.Gentzen.bounded3Closure) (T := ProjectSelfTest.Consequence.Gentzen.valid)

@[answers "silmaril.selftest.consequence.gentzen.bounded3_closure_sound" thm]
public theorem bounded3_closure_sound : ∀ Γ Δ, SoundAt bounded3Closure valid Γ Δ :=
  derives_viaUnsat_le_valid (bounded_sound 3) lneg_complete

silmaril instance silmaril.selftest.consequence.gentzen.bounded3_complete_closure (expect := CSA)
  (title := "The bounded test is complete for its closure (fails: not cut-closed)") :=
  silmaril.shapes.consequence.complete_at
  (S := ProjectSelfTest.Consequence.Gentzen.viaUnsatBounded3)
  (T := ProjectSelfTest.Consequence.Gentzen.bounded3Closure)

@[answers "silmaril.selftest.consequence.gentzen.bounded3_complete_closure" csa]
public theorem bounded3_complete_closure :
    ∃ Γ Δ, ¬ CompleteAt viaUnsatBounded3 bounded3Closure Γ Δ :=
  ⟨[(true, 0), (true, 2), (true, 1)], [(true, 0)], fun h => absurd (h
    (.cut (Γ := [(true, 0), (true, 2)]) (Γ' := [(true, 1)]) (Δ := []) (Δ' := [(true, 0)])
      (a := (true, 0)) trivial (.base (by decide)) (.base (by decide))))
    (by decide : ¬ viaUnsat (bounded 3) lneg [(true, 0), (true, 2), (true, 1)] [(true, 0)])⟩

silmaril instance silmaril.selftest.consequence.gentzen.chain_closure_p_r (expect := THM)
  (title := "p ⊢ r in the closure of p ⊢ q, q ⊢ r (by cut)") := silmaril.shapes.consequence.derives
  (S := ProjectSelfTest.Consequence.Gentzen.chainClosure) (Γ := [(true, 0)]) (φ := [(true, 2)])

@[answers "silmaril.selftest.consequence.gentzen.chain_closure_p_r" thm]
public theorem chain_closure_p_r : Derives chainClosure [(true, 0)] [(true, 2)] :=
  .cut (Γ := [(true, 0)]) (Γ' := []) (Δ := []) (Δ' := [(true, 2)]) trivial
    (.base (.inl ⟨rfl, rfl⟩)) (.base (.inr ⟨rfl, rfl⟩))

silmaril instance silmaril.selftest.consequence.gentzen.chain_p_r (expect := UNS)
  (title := "p ⊢ r in the raw sequents (fails: no cut)") := silmaril.shapes.consequence.derives
  (S := ProjectSelfTest.Consequence.Gentzen.chainRaw) (Γ := [(true, 0)]) (φ := [(true, 2)])

@[answers "silmaril.selftest.consequence.gentzen.chain_p_r" csa]
public theorem chain_p_r : ¬ Derives chainRaw [(true, 0)] [(true, 2)] := by
  rintro (⟨-, h⟩ | ⟨h, -⟩) <;> simp_all

end

silmaril group silmaril.selftest.consequence.gentzen (title := "Consequence systems: literal sequents (Gentzen)")
  (children := [silmaril.selftest.consequence.gentzen.taut_restriction_sound,
    silmaril.selftest.consequence.gentzen.taut_restriction_complete,
    silmaril.selftest.consequence.gentzen.identity_closed,
    silmaril.selftest.consequence.gentzen.identity_restriction_sound,
    silmaril.selftest.consequence.gentzen.restriction_sound,
    silmaril.selftest.consequence.gentzen.restriction_complete, silmaril.selftest.consequence.gentzen.pairs_up_closed,
    silmaril.selftest.consequence.gentzen.pairs_set_inv, silmaril.selftest.consequence.gentzen.bounded3_up_closed,
    silmaril.selftest.consequence.gentzen.pairs_closed,
    silmaril.selftest.consequence.gentzen.bounded3_closed, silmaril.selftest.consequence.gentzen.pairs_sound,
    silmaril.selftest.consequence.gentzen.pairs_complete, silmaril.selftest.consequence.gentzen.p_qp,
    silmaril.selftest.consequence.gentzen.p_q, silmaril.selftest.consequence.gentzen.bounded3_sound,
    silmaril.selftest.consequence.gentzen.bounded3_closure_sound,
    silmaril.selftest.consequence.gentzen.bounded3_complete_closure,
    silmaril.selftest.consequence.gentzen.chain_closure_p_r,
    silmaril.selftest.consequence.gentzen.chain_p_r])
