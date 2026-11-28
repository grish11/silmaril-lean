module

public import Silmaril.SSA.Isotope.LambdaSSA.Flat.Thms
public import Silmaril.SSA.Isotope.LetCase.Thms

/-! # Materialize a leading operand let at a flat jump -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize

open LambdaSSA (FiniteCFG Flat)
open LetCase.LocallyNameless (Tm)

universe u
variable {F : Type u} {labels blocks exits n : Nat}

/-- Replace a locally bound alias by its original variable and remove
the alias binder. The map shifts every other variable back into scope. -/
def aliasIndex (i : Fin n) : Fin (n + 1) → Fin n :=
  Fin.cases i id

/-- A row-level let may bind a computed jump operand. A case arm in the
named grammar is a terminator, so there we only contract a variable alias. -/
def jump (canBind : Bool) (target : Fin labels) (arg : Tm Empty F n) : Flat F labels n :=
  match arg with
  | .let₁ a tail =>
    if canBind then .let₁ a (.br target tail)
    else match a with
      | .bv i => .br target (tail.rename (aliasIndex i))
      | _ => .br target arg
  | _ => .br target arg

/-- Preserve every label and branch choice. Materialize at jumps only,
including jumps following written let prefixes. -/
def body (canBind : Bool) : {m : Nat} → Flat F labels m → Flat F labels m
  | _, .br target arg => jump canBind target arg
  | _, .let₁ a tail => .let₁ a (body canBind tail)
  | _, .let₂ a tail => .let₂ a (body canBind tail)
  | _, .case a l r => .case a (body false l) (body false r)

/-- Keep the caller context and label positions of the actual table. -/
def graph (g : FiniteCFG F blocks exits n) : FiniteCFG F blocks exits n :=
  ⟨body true g.entry, fun i => body true (g.block i)⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize
