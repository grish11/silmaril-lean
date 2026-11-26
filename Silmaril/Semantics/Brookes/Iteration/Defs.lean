module

public import Silmaril.Semantics.Brookes.Thms
public import Silmaril.Semantics.Brookes.Parallel.Defs
public import Silmaril.Semantics.Domain.Kleene
public import Silmaril.Semantics.Elgot.Defs

@[expose] public section

namespace Silmaril.Semantics.Brookes.Behavior

universe u v w x

open OmegaCompletePartialOrder

variable {Store : Type u} {X : Type v} {Y : Type w} {D : Type x}

/-- Union preserves nonempty words and closure, regardless of the index set. -/
def union {ι : Type*} (behaviors : ι → Behavior Store Y) : Behavior Store Y where
  accepts trace y := ∃ i, (behaviors i).accepts trace y
  nonempty := by
    rintro _ _ ⟨i, h⟩
    exact (behaviors i).nonempty h
  stable := by
    rintro _ _ _ ⟨i, h⟩ step
    exact ⟨i, (behaviors i).stable h step⟩

/-- Behaviors are ordered by inclusion of open word and result observations. -/
instance : OmegaCompletePartialOrder (Behavior Store Y) where
  le p q := ∀ ⦃trace result⦄, p.accepts trace result → q.accepts trace result
  le_refl _ _ _ h := h
  le_trans _ _ _ hp hq _ _ h := hq (hp h)
  le_antisymm p q hp hq := Behavior.ext (fun _ _ => ⟨fun h => hp h, fun h => hq h⟩)
  ωSup c := union c
  le_ωSup _ n _ _ h := ⟨n, h⟩
  ωSup_le _ _ h := by rintro _ _ ⟨n, hn⟩; exact h n hn

/-- The empty behavior has no completed observations. -/
instance : OrderBot (Behavior Store Y) where
  bot := ⟨fun _ _ => False, fun _ _ h => h.elim, fun _ _ _ h _ => h.elim⟩
  bot_le _ _ _ h := h.elim

/-- One unfolding of a loop. The left summand returns and the right summand recurs. -/
def unfoldLoop (body : X → Behavior Store (Y ⊕ X)) (next : X → Behavior Store Y) :
    X → Behavior Store Y :=
  fun x => (body x).bind (Sum.elim ret next)

/-- The behavior produced using at most the given number of calls of the body. -/
def approx (body : X → Behavior Store (Y ⊕ X)) : Nat → X → Behavior Store Y
  | 0 => ⊥
  | n + 1 => unfoldLoop body (approx body n)

/-- All finite completed observations of the loop, as the union of its approximants. -/
def iterate (body : X → Behavior Store (Y ⊕ X)) (x : X) : Behavior Store Y :=
  union fun n => approx body n x

/-- Carry a pure context through each call of a loop. -/
def strengthBody (body : X → Behavior Store (Y ⊕ X)) :
    D × X → Behavior Store ((D × Y) ⊕ (D × X)) :=
  fun (d, x) => (body x).mapResult (Sum.map (fun y => (d, y)) (fun next => (d, next)))

instance : Monad (Behavior Store) where
  pure := ret
  bind := bind

instance : LawfulMonad (Behavior Store) := LawfulMonad.mk'
  (id_map := bind_ret)
  (pure_bind := ret_bind)
  (bind_assoc := bind_assoc)

instance : Elgot.Iterate (Behavior Store) where
  iter := iterate

end Silmaril.Semantics.Brookes.Behavior
