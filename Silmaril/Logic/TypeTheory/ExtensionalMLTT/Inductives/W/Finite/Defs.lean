module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.SetSemantics.Defs
public import Silmaril.Logic.SetTheory.Universes.Finite.Defs
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Discrete.Basic

@[expose] public section

/-!
# MLTT with a finite supply of universes

`MLTT(n)` has judgments mentioning only levels strictly below `n`. Its models
are actual finite towers of `n` Grothendieck universes. The bound checks the
whole judgment, including context types and annotations erased by semantics.

This bounds sentence syntax. A derivation with a bounded conclusion may use
higher levels internally. `Finite.Derivation` bounds every inference-rule
universe and proves soundness in these finite models.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

universe u

/-- One more than the largest universe index in a term, or zero if none occur.

Every annotation is included, even when its interpretation is erased.
-/
def Tm.universeBound : {k : ℕ} → Tm k → ℕ
  | _, .univ n => n + 1
  | _, .fv _ | _, .bv _ | _, .empty | _, .unit | _, .star | _, .nats | _, .zero => 0
  | _, .succ t | _, .fst t | _, .snd t | _, .refl t => t.universeBound
  | _, .pi A B | _, .sigma A B | _, .abs A B | _, .app A B | _, .pair A B |
      _, .absurd A B => max A.universeBound B.universeBound
  | _, .natrec C s z n =>
      max (max C.universeBound s.universeBound) (max z.universeBound n.universeBound)
  | _, .id A a b => max A.universeBound (max a.universeBound b.universeBound)

  | _, .wtype A B => max A.universeBound B.universeBound
  | _, .sup A B a f => max (max A.universeBound B.universeBound)
      (max a.universeBound f.universeBound)
  | _, .wrec A B C s t => max (max A.universeBound B.universeBound)
      (max C.universeBound (max s.universeBound t.universeBound))

/-- Every universe occurrence in the term has index strictly below `n`. -/
def Tm.UsesBelow {k : ℕ} (t : Tm k) (n : ℕ) : Prop := t.universeBound ≤ n

/-- Universe bound of all types declared in a context. -/
def Ctx.universeBound : Ctx → ℕ
  | .nil => 0
  | .cons Γ _ A => max Γ.universeBound A.universeBound

/-- All context types use universe levels strictly below `n`. -/
def Ctx.UsesBelow (Γ : Ctx) (n : ℕ) : Prop := Γ.universeBound ≤ n

/-- Universe bound of a judgment's context, type and both terms. -/
def Jdg.universeBound (j : Jdg) : ℕ :=
  max (max j.Γ.universeBound j.A.universeBound) (max j.a.universeBound j.b.universeBound)

/-- The whole judgment uses universe levels strictly below `n`. -/
def Jdg.UsesBelow (j : Jdg) (n : ℕ) : Prop := j.universeBound ≤ n

namespace Finite

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic.SetTheory

/-- Sentences of the fragment `MLTT(n)`. -/
abbrev Sentence (n : ℕ) := {j : Jdg // j.UsesBelow n}

/-- Bounded judgments interpreted in finite towers, without an infinite model. -/
def room (n : ℕ) : Room.{0, u + 1, u + 1} where
  Sen := Sentence n
  Mod := Cat.of (Discrete (FiniteTower.{u} n))
  Sat T j := j.val.ValidIn (Discrete.as T).U

/-- The fixed-language institution `MLTT(n)`, with finite-tower models. -/
def inst (n : ℕ) : Discrete Unit ⥤ Room.{0, u + 1, u + 1} :=
  Discrete.functor fun _ => room.{u} n

/-- Bundled finite-universe MLTT institution for institution and Hets APIs. -/
def bundled (n : ℕ) : Inst.{0, 0, 0, u + 1, u + 1} where
  Sign := Discrete Unit
  I := inst.{u} n

end Finite

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
