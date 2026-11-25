module

public import Silmaril.Semantics.Calco2019.Examples.SetModels.Thms

/-! # The nonempty powerset monad -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.SetModels.NonemptyPowerset

variable {X Y : Type u}

instance : Monad (NonemptyPowerset.{u}) where
  pure x := ⟨pure x, ⟨x, Elgot.Nondet.mem_pure x⟩⟩
  bind p f := ⟨p.1 >>= fun x => (f x).1, by
    obtain ⟨x, hx⟩ := p.2
    obtain ⟨y, hy⟩ := (f x).2
    exact ⟨y, Elgot.Nondet.mem_bind_iff.mpr ⟨x, hx, hy⟩⟩⟩

@[simp] theorem val_pure (x : X) : (pure x : NonemptyPowerset X).1 = pure x := rfl

@[simp] theorem val_bind (p : NonemptyPowerset X) (f : X → NonemptyPowerset Y) :
    (p >>= f).1 = p.1 >>= fun x => (f x).1 := rfl

/-- The CALCO guard demands at least one direct return at every state. -/
def Guarded {Z : Type u} (f : X → NonemptyPowerset (Y ⊕ Z)) : Prop :=
  HasDirectReturn fun x => (f x).1

end Silmaril.Calco2019.Examples.SetModels.NonemptyPowerset
