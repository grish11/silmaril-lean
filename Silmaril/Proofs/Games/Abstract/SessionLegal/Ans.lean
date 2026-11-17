module

public import Silmaril.Games.Abstract.SessionLegal.Defs
public import Silmaril.Games.DivCompAns.Defs

/-!
# Legality of plays whose answers are legal at every store (proofs)

See `Silmaril.Games.Abstract.SessionLegal.Thms`: the log of a running or waiting state of the
threading automaton consists of answers of the play, so a play all of whose import answers satisfy
a store-independent `R` reaches only states whose logs do.
-/

public section

namespace Silmaril.Proofs.Games.Abstract.SessionLegal

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread Silmaril.Games.Abstract.StratSession
open Silmaril.Games.Abstract.SessionLegal

universe u

variable {E : Sig.{u}} {S A B : Type u} {Lg : S → A → List (Call E) → Prop}
  {R : (m : E.Op) → E.Ar m → Prop}

/-- The log of a running or waiting state answers in `R`. -/
def LogIn (R : (m : E.Op) → E.Ar m → Prop) : TSt E S A → Prop
  | .run _ _ c => ∀ x ∈ c, R x.1 x.2
  | .wait _ _ c _ => ∀ x ∈ c, R x.1 x.2
  | _ => True

theorem tRun_logIn {f : AFun E S A B} {P : Pending E S A} {x y : TSt E S A}
    {p : List (Move E (sig1 A B))} (hr : TRun f P x p y) (hx : LogIn R x) (hp : LAnsIn R p) :
    LogIn R y := by
  induction hr with
  | nil => exact hx
  | cons hst _ ih =>
    refine ih ?_ fun m n hm => hp m n (List.mem_cons_of_mem _ hm)
    cases hst with
    | ask => intro _ hx; simp at hx
    | call => exact hx
    | reply s a c m n =>
      intro x hxc
      rcases List.mem_append.1 hxc with hxc | hxc
      · exact hx x hxc
      · rw [List.mem_singleton] at hxc
        subst hxc
        exact hp m n List.mem_cons_self
    | ret => trivial
    | trap => trivial
    | deadAsk => trivial

theorem legalAtS_of_lAnsIn {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}
    (hR : ∀ s a c, (∀ x ∈ c, R x.1 x.2) → Lg s a c) {q : List (Move E (sig1 A B))}
    (hq : LAnsIn R q) : LegalAtS Lg t s₀ q := by
  rintro p y rfl hr
  have hp : LAnsIn R p := fun m n hm => hq m n (List.mem_map_of_mem (f := relMove) hm)
  have hy := tRun_logIn hr trivial hp
  cases y with
  | run s a c => exact hR s a c hy
  | wait s a c m => exact hR s a c hy
  | idle => trivial
  | dead => trivial
  | stuck => trivial

theorem sLegal_of_lAnsIn {t : ObsTriple E S A (B ⊕ PUnit.{u + 1})} {s₀ : S}
    (hR : ∀ s a c, (∀ x ∈ c, R x.1 x.2) → Lg s a c) {q : List (Move E (sig1 A B))}
    (hq : LAnsIn R q) : SLegal Lg t s₀ q := by
  refine ⟨?_, legalAtS_of_lAnsIn hR hq⟩
  rintro q₁ o q₂ rfl -
  exact legalAtS_of_lAnsIn hR fun m n hm => hq m n (List.mem_append_left _ hm)

end Silmaril.Proofs.Games.Abstract.SessionLegal
