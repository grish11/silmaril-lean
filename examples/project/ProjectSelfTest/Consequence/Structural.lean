module

public import Silmaril.Project.Shapes.Consequence.Thms
public import Silmaril.Logic.Consequence.Gentzen.Translate.Examples
public import Silmaril.Logic.Consequence.Gentzen.Finitary.Examples
public import Silmaril.Logic.Consequence.Gentzen.Finitary.Thms
public import Silmaril.Logic.Consequence.Gentzen.Examples

/-!
# The `sil project` self-test: translations, signed lifts, finite sets and sets

Systems of the structural track's modules, answered by their own theorems:

* **A signed lift** (`Gentzen.Translate`): the identity calculus on atoms `ℕ` and its lift
  `signedLift identity` to signed literals. The lift proves explosion `p, ¬p ⊢` and excluded
  middle `⊢ p, ¬p`; along `Signed.pos` on both sides it translates the identity calculus and
  reflects it (`posPart_signedLift`).
* **Finite sets and sets** (`Gentzen.Finitary`): validity of literal sequents read on finite
  sets (`onFinset`) and on sets (`onSet`); along the inclusion of finite sets in sets the two
  agree (`onFinset_iff_onSet`, ordinary weakening). Over `ℕ` with `m ⊨ n ↔ m ≠ n`, the
  set reading of finite validity is sound for infinitary validity but not complete:
  `ℕ ⊨ ∅` holds infinitarily and has no finite witness (`not_onSet_valid`; no compactness).
-/

namespace ProjectSelfTest.Consequence.Structural

open Silmaril.Consequence Silmaril.Consequence.Gentzen

@[expose] public section

/-- The pure identity calculus on atoms. -/
def identity : Seq ℕ := Translate.Examples.identity
/-- Its lift to signed literals. -/
def identitySigned : Seq (Signed ℕ) := signedLift Translate.Examples.identity

/-- The identity calculus reindexed along `succ` on both sides (`System.pullback`). -/
def identityRenamed : Seq ℕ :=
  System.pullback (List.map Nat.succ) (List.map Nat.succ) Translate.Examples.identity

/-- Validity of literal sequents on finite sets. -/
noncomputable def validFinset : System (Finset Examples.Lit) (Finset Examples.Lit) :=
  onFinset (Valid Examples.lsat)
/-- Validity of literal sequents on sets (some finite subsets form a valid sequent). -/
def validSet : System (Set Examples.Lit) (Set Examples.Lit) := onSet (Valid Examples.lsat)

/-- Finite validity read on sets, over `m ⊨ n ↔ m ≠ n`. -/
def neqOnSet : System (Set ℕ) (Set ℕ) := onSet (Valid Finitary.Examples.neq)
/-- Infinitary validity over `m ⊨ n ↔ m ≠ n`. -/
def neqInf : System (Set ℕ) (Set ℕ) := InfValid Finitary.Examples.neq

end

end ProjectSelfTest.Consequence.Structural

silmaril consequence_system silmaril.selftest.consequence.structural.identity :=
  ProjectSelfTest.Consequence.Structural.identity (title := "The identity calculus on atoms ℕ (Derives defaultRules ⊥)")
silmaril consequence_system silmaril.selftest.consequence.structural.identity_signed :=
  ProjectSelfTest.Consequence.Structural.identitySigned (title := "Its signed lift: negative literals change sides")
silmaril consequence_system silmaril.selftest.consequence.structural.identity_renamed :=
  ProjectSelfTest.Consequence.Structural.identityRenamed (title := "The identity calculus pulled back along succ")
silmaril consequence_system silmaril.selftest.consequence.structural.valid_finset :=
  ProjectSelfTest.Consequence.Structural.validFinset (title := "Valid literal sequents on finite sets (onFinset)")
silmaril consequence_system silmaril.selftest.consequence.structural.valid_set :=
  ProjectSelfTest.Consequence.Structural.validSet (title := "Valid literal sequents on sets (onSet: a finite witness)")
silmaril consequence_system silmaril.selftest.consequence.structural.neq_on_set :=
  ProjectSelfTest.Consequence.Structural.neqOnSet (title := "Finite validity on sets over m ⊨ n ↔ m ≠ n")
silmaril consequence_system silmaril.selftest.consequence.structural.neq_inf :=
  ProjectSelfTest.Consequence.Structural.neqInf (title := "Infinitary validity over m ⊨ n ↔ m ≠ n")

open ProjectSelfTest.Consequence.Structural Silmaril.Consequence Silmaril.Consequence.Gentzen
  Silmaril.Project.Shapes.Consequence in
section

silmaril instance silmaril.selftest.consequence.structural.lift_explosion (expect := THM)
  (title := "p, ¬p ⊢ in the signed lift") := silmaril.shapes.consequence.derives
  (S := ProjectSelfTest.Consequence.Structural.identitySigned)
  (Γ := [Silmaril.Consequence.Signed.pos 0, Silmaril.Consequence.Signed.neg 0]) (φ := [])

@[answers "silmaril.selftest.consequence.structural.lift_explosion" thm]
public theorem lift_explosion : Derives identitySigned [.pos 0, .neg 0] [] :=
  Translate.Examples.identity_lift_explosion

silmaril instance silmaril.selftest.consequence.structural.lift_excluded_middle (expect := THM)
  (title := "⊢ p, ¬p in the signed lift") := silmaril.shapes.consequence.derives
  (S := ProjectSelfTest.Consequence.Structural.identitySigned) (Γ := [])
  (φ := [Silmaril.Consequence.Signed.pos 0, Silmaril.Consequence.Signed.neg 0])

@[answers "silmaril.selftest.consequence.structural.lift_excluded_middle" thm]
public theorem lift_excluded_middle : Derives identitySigned [] [.pos 0, .neg 0] :=
  Translate.Examples.identity_lift_excluded_middle

silmaril instance silmaril.selftest.consequence.structural.lift_translates (expect := THM)
  (title := "Signed.pos translates the identity calculus into its signed lift") :=
  silmaril.shapes.consequence.translates_at (S := ProjectSelfTest.Consequence.Structural.identity)
  (T := ProjectSelfTest.Consequence.Structural.identitySigned)
  (f := List.map Silmaril.Consequence.Signed.pos) (g := List.map Silmaril.Consequence.Signed.pos)

@[answers "silmaril.selftest.consequence.structural.lift_translates" thm]
public theorem lift_translates : ∀ Γ Δ, TranslatesAt identity identitySigned
    (List.map Signed.pos) (List.map Signed.pos) Γ Δ := fun Γ Δ h =>
  (congrFun (congrFun Translate.Examples.identity_lift_posPart Γ) Δ).mpr h

silmaril instance silmaril.selftest.consequence.structural.lift_reflects (expect := THM)
  (title := "…and reflects it (posPart_signedLift)") :=
  silmaril.shapes.consequence.reflects_at (S := ProjectSelfTest.Consequence.Structural.identity)
  (T := ProjectSelfTest.Consequence.Structural.identitySigned)
  (f := List.map Silmaril.Consequence.Signed.pos) (g := List.map Silmaril.Consequence.Signed.pos)

@[answers "silmaril.selftest.consequence.structural.lift_reflects" thm]
public theorem lift_reflects : ∀ Γ Δ, ReflectsAt identity identitySigned
    (List.map Signed.pos) (List.map Signed.pos) Γ Δ := fun Γ Δ h =>
  (congrFun (congrFun Translate.Examples.identity_lift_posPart Γ) Δ).mp h

-- closure certificates transported along the lift and along a pullback (rule profile: defaultRules)
silmaril instance silmaril.selftest.consequence.structural.lift_closed (expect := THM)
  (title := "The signed lift is closed under the default rules (closed_signedLift)") :=
  silmaril.shapes.consequence.gentzen_closed (rs := Silmaril.Consequence.Gentzen.defaultRules)
  (S := ProjectSelfTest.Consequence.Structural.identitySigned)

@[answers "silmaril.selftest.consequence.structural.lift_closed" thm]
public theorem lift_closed : GentzenClosed defaultRules identitySigned :=
  closed_signedLift (derives_closed defaultRules ⊥)

silmaril instance silmaril.selftest.consequence.structural.renamed_closed (expect := THM)
  (title := "The pullback along succ is closed under the default rules (closed_pullback, Rules.Hom.default)") :=
  silmaril.shapes.consequence.gentzen_closed (rs := Silmaril.Consequence.Gentzen.defaultRules)
  (S := ProjectSelfTest.Consequence.Structural.identityRenamed)

@[answers "silmaril.selftest.consequence.structural.renamed_closed" thm]
public theorem renamed_closed : GentzenClosed defaultRules identityRenamed :=
  closed_pullback (Rules.Hom.default Nat.succ) (derives_closed defaultRules ⊥)

silmaril instance silmaril.selftest.consequence.structural.renamed_translates (expect := THM)
  (title := "succ translates the pullback into the identity calculus (by definition of pullback)") :=
  silmaril.shapes.consequence.translates_at (S := ProjectSelfTest.Consequence.Structural.identityRenamed)
  (T := ProjectSelfTest.Consequence.Structural.identity) (f := List.map Nat.succ) (g := List.map Nat.succ)

@[answers "silmaril.selftest.consequence.structural.renamed_translates" thm]
public theorem renamed_translates : ∀ Γ Δ, TranslatesAt identityRenamed identity
    (List.map Nat.succ) (List.map Nat.succ) Γ Δ := fun _ _ h => h

silmaril instance silmaril.selftest.consequence.structural.renamed_reflects (expect := THM)
  (title := "…and reflects it") :=
  silmaril.shapes.consequence.reflects_at (S := ProjectSelfTest.Consequence.Structural.identityRenamed)
  (T := ProjectSelfTest.Consequence.Structural.identity) (f := List.map Nat.succ) (g := List.map Nat.succ)

@[answers "silmaril.selftest.consequence.structural.renamed_reflects" thm]
public theorem renamed_reflects : ∀ Γ Δ, ReflectsAt identityRenamed identity
    (List.map Nat.succ) (List.map Nat.succ) Γ Δ := fun _ _ h => h

silmaril instance silmaril.selftest.consequence.structural.finset_to_set (expect := THM)
  (title := "Finite sets as sets translate valid sequents (onFinset_iff_onSet)") :=
  silmaril.shapes.consequence.translates_at (S := ProjectSelfTest.Consequence.Structural.validFinset)
  (T := ProjectSelfTest.Consequence.Structural.validSet)
  (f := fun (s : Finset Silmaril.Consequence.Gentzen.Examples.Lit) => (↑s : Set Silmaril.Consequence.Gentzen.Examples.Lit))
  (g := fun (s : Finset Silmaril.Consequence.Gentzen.Examples.Lit) => (↑s : Set Silmaril.Consequence.Gentzen.Examples.Lit))

@[answers "silmaril.selftest.consequence.structural.finset_to_set" thm]
public theorem finset_to_set : ∀ s t, TranslatesAt validFinset validSet
    (fun (s : Finset Examples.Lit) => (↑s : Set Examples.Lit))
    (fun (s : Finset Examples.Lit) => (↑s : Set Examples.Lit)) s t := fun s t h =>
  (onFinset_iff_onSet valid_closed.weak s t).mp h

silmaril instance silmaril.selftest.consequence.structural.finset_from_set (expect := THM)
  (title := "…and reflect them") :=
  silmaril.shapes.consequence.reflects_at (S := ProjectSelfTest.Consequence.Structural.validFinset)
  (T := ProjectSelfTest.Consequence.Structural.validSet)
  (f := fun (s : Finset Silmaril.Consequence.Gentzen.Examples.Lit) => (↑s : Set Silmaril.Consequence.Gentzen.Examples.Lit))
  (g := fun (s : Finset Silmaril.Consequence.Gentzen.Examples.Lit) => (↑s : Set Silmaril.Consequence.Gentzen.Examples.Lit))

@[answers "silmaril.selftest.consequence.structural.finset_from_set" thm]
public theorem finset_from_set : ∀ s t, ReflectsAt validFinset validSet
    (fun (s : Finset Examples.Lit) => (↑s : Set Examples.Lit))
    (fun (s : Finset Examples.Lit) => (↑s : Set Examples.Lit)) s t := fun s t h =>
  (onFinset_iff_onSet valid_closed.weak s t).mpr h

silmaril instance silmaril.selftest.consequence.structural.neq_sound (expect := THM)
  (title := "Finite validity on sets is sound for infinitary validity") :=
  silmaril.shapes.consequence.sound_at (S := ProjectSelfTest.Consequence.Structural.neqOnSet)
  (T := ProjectSelfTest.Consequence.Structural.neqInf)

@[answers "silmaril.selftest.consequence.structural.neq_sound" thm]
public theorem neq_sound : ∀ A B, SoundAt neqOnSet neqInf A B := fun _ _ h => onSet_valid_sound h

silmaril instance silmaril.selftest.consequence.structural.neq_complete (expect := CSA)
  (title := "Finite validity on sets is complete for infinitary validity (fails: ℕ ⊨ ∅, no compactness)") :=
  silmaril.shapes.consequence.complete_at (S := ProjectSelfTest.Consequence.Structural.neqOnSet)
  (T := ProjectSelfTest.Consequence.Structural.neqInf)

@[answers "silmaril.selftest.consequence.structural.neq_complete" csa]
public theorem neq_complete : ∃ A B, ¬ CompleteAt neqOnSet neqInf A B :=
  ⟨Set.univ, ∅, fun h => Finitary.Examples.not_onSet_valid (h Finitary.Examples.infValid_univ)⟩

end

silmaril group silmaril.selftest.consequence.structural
  (title := "Translations, signed lifts, finite sets and sets (structural track)")
  (children := [silmaril.selftest.consequence.structural.lift_closed,
    silmaril.selftest.consequence.structural.renamed_closed,
    silmaril.selftest.consequence.structural.renamed_translates,
    silmaril.selftest.consequence.structural.renamed_reflects,
    silmaril.selftest.consequence.structural.lift_explosion,
    silmaril.selftest.consequence.structural.lift_excluded_middle,
    silmaril.selftest.consequence.structural.lift_translates,
    silmaril.selftest.consequence.structural.lift_reflects,
    silmaril.selftest.consequence.structural.finset_to_set,
    silmaril.selftest.consequence.structural.finset_from_set,
    silmaril.selftest.consequence.structural.neq_sound,
    silmaril.selftest.consequence.structural.neq_complete])
