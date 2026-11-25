module

public import Silmaril.Semantics.Calco2019.Maybe.LoopDecomposition.Thms
public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms
public import Silmaril.Semantics.ElgotMonads.Thms

/-! # Maybe on the category of types -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Maybe.Types

abbrev Model (X : Type u) := X ⊕ PUnit.{u + 1}

instance : Monad Model where
  pure := Sum.inl
  bind x f := x.elim f Sum.inr

/-- The optional result type is classically equivalent to the library's partiality type. -/
noncomputable def observe (X : Type u) : Part X ≃ Model X :=
  Part.equivOption.trans (Equiv.optionEquivSumPUnit X)

noncomputable instance : Elgot.Iterate Model where
  iter f x := observe _ (Elgot.iter (fun x => (observe _).symm (f x)) x)

/-- The result, if any, of a pure loop that returns after exactly `n` recursive steps. -/
def exitAt {X Y : Type u} (f : X → Y ⊕ X) : ℕ → X → Option Y
  | 0, x => (f x).elim some (fun _ => none)
  | n + 1, x => (f x).elim (fun _ => none) (exitAt f n)

end Silmaril.Calco2019.Maybe.Types
