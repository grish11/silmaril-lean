module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Paths.Thms
public import Silmaril.Semantics.Calco2019.Examples.Printing.TraceMonad.Thms
public import Silmaril.Semantics.Calco2019.Examples.TypeKleisli.Thms
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Action.Defs

/-! # Deterministic writers extended by a left action -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Printing

/-- A finite word and result, or a terminal observation in the action carrier. -/
abbrev WriterAction (A M X : Type u) := (List A × X) ⊕ M

namespace WriterAction

variable {A M X Y : Type u}

def prependOutput [MulAction (FreeMonoid A) M] (word : List A) : WriterAction A M X → WriterAction A M X
  | .inl (suffix, x) => .inl (word ++ suffix, x)
  | .inr m => .inr (FreeMonoid.ofList word • m)

def pureOutput (x : X) : WriterAction A M X := .inl ([], x)

def bind [MulAction (FreeMonoid A) M] (p : WriterAction A M X)
    (k : X → WriterAction A M Y) : WriterAction A M Y :=
  match p with
  | .inl (word, x) => prependOutput word (k x)
  | .inr m => .inr m

instance [MulAction (FreeMonoid A) M] : Monad (WriterAction A M) where
  pure := pureOutput
  bind := bind

/-- A recursive return after the empty word is the sole prohibited observation. -/
def Guarded {Z : Type u} (f : X → WriterAction A M (Y ⊕ Z)) : Prop :=
  ∀ x z, f x ≠ .inl ([], .inr z)

/-- The separating writer loop prints one letter and calls itself. -/
def letterLoop (a : A) (x : PUnit.{u + 1}) :
    WriterAction A M (PUnit.{u + 1} ⊕ PUnit.{u + 1}) := .inl ([a], .inr x)

/-- The action which prepends a finite word to an infinite stream. -/
@[instance_reducible] def streamAction (A : Type u) : MulAction (FreeMonoid A) (ℕ → A) where
  smul w s := w.toList.foldr cons s
  one_smul _ := rfl
  mul_smul w v s := by
    change (w.toList ++ v.toList).foldr cons s = w.toList.foldr cons (v.toList.foldr cons s)
    rw [List.foldr_append]

/-- The singleton action forgets every prepended word. -/
@[instance_reducible] def singletonAction (A : Type u) : MulAction (FreeMonoid A) PUnit.{u + 1} where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The action on the empty type recovers the ordinary writer carrier. -/
@[instance_reducible] def emptyAction (A : Type u) : MulAction (FreeMonoid A) PEmpty.{u + 1} where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Nonempty finite words also form a left action by prefixing. -/
@[instance_reducible] def nonemptyWordAction (A : Type u) : MulAction (FreeMonoid A) {w : List A // w ≠ []} where
  smul w v := ⟨w.toList ++ v.1, fun h => v.2 (List.append_eq_nil_iff.mp h).2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := Subtype.ext (List.append_assoc _ _ _)

end WriterAction
end Silmaril.Calco2019.Examples.Printing
