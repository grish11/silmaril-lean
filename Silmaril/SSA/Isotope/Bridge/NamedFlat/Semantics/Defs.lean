module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Defs

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

open Silmaril.SSA.LambdaRTL

universe u
variable {V K F α : Type u} {n labels : Nat}

/-- Named execution over the same tagged values as Isotope. Structural
destructors are partial, and primitives share a partial implementation. -/
def model (prim : F → Value α → Part (Value α)) : Model F Part (Value α) where
  unit := .unit
  pair := .pair
  inl := .inl
  inr := .inr
  unpair
    | .pair a b => Part.some (a, b)
    | _ => Part.none
  split
    | .inl a => Part.some (.inl a)
    | .inr b => Part.some (.inr b)
    | _ => Part.none
  app := prim
  abort _ := Part.none

/-- Isotope's finite primitive relation for a stateless partial implementation. -/
def instr (prim : F → Value α → Part (Value α)) :
    F → Value α → Unit → Value α → Unit → Prop :=
  fun f arg _ result _ => result ∈ prim f arg

/-- The positional values agree at every name exported by the binding map. -/
def Agrees (names : Names V n) (store : V → Value α) (env : LambdaSSA.Semantics.Env α) : Prop :=
  ∀ reg slot, names reg = some slot → env slot.val = store reg

/-- Express a named result in the flat table's internal-plus-external coordinates. -/
def number (index : K → Option (Fin labels)) (result : K × Value α) :
    Part (Nat × Value α) :=
  match index result.1 with
  | some slot => Part.some (slot.val, result.2)
  | none => Part.none

end Silmaril.Isotope.Bridge.NamedFlat
