module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Provenance.Defs

/-! # Executable checks of structural entry and packet-only row scope -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

open LambdaSSA (Flat Region)
open LetCase.LocallyNameless (Tm)
open Morphism.CaseSSA (erase ofScoped erase_ofScoped)
open Silmaril.SSA.LambdaRTL (Val)

variable {F : Type} {n : Nat}

def scopedTerm (n : Nat) (t : LambdaSSA.Tm F) : Option {v : Tm Empty F n // erase v = t} :=
  if h : t.Scoped n then some ⟨ofScoped t h, erase_ofScoped t h⟩ else none

/-- Recover the finite labels and exact variable scope of an erased flat
body. Successful reconstruction carries its actual erasure equation. -/
def scopedRow (labels : Nat) : (n : Nat) → (r : Region F) →
    Option {row : Flat F labels n // row.erase = r}
  | n, .br label arg => do
    if h : label < labels then
      let arg' ← scopedTerm n arg
      return ⟨.br ⟨label, h⟩ arg'.val, congrArg (Region.br label) arg'.property⟩
    else none
  | n, .let₁ arg body => do
    let arg' ← scopedTerm n arg
    let body' ← scopedRow labels (n + 1) body
    return ⟨.let₁ arg'.val body'.val, congrArg₂ Region.let₁ arg'.property body'.property⟩
  | n, .let₂ arg body => do
    let arg' ← scopedTerm n arg
    let body' ← scopedRow labels (n + 2) body
    return ⟨.let₂ arg'.val body'.val, congrArg₂ Region.let₂ arg'.property body'.property⟩
  | n, .case arg left right => do
    let arg' ← scopedTerm n arg
    let left' ← scopedRow labels (n + 1) left
    let right' ← scopedRow labels (n + 1) right
    return ⟨.case arg'.val left'.val right'.val, by
      change Region.case (erase arg'.val) left'.val.erase right'.val.erase = _
      rw [arg'.property, left'.property, right'.property]⟩
  | _, .cfg .. => none

/-- Check both rows in a shared packet-only scope before comparing their
literal syntax. Context sizes before erasure may differ. -/
def commonRow [DecidableEq F] (labels : Nat) (source target : Region F) :
    Option {row : Flat F labels 1 // source = row.erase ∧ target = row.erase} := do
  let l ← scopedRow labels 1 source
  let r ← scopedRow labels 1 target
  if h : l.val = r.val then
    return ⟨l.val, l.property.symm, r.property.symm.trans (congrArg Flat.erase h.symm)⟩
  else none

/-- Recover a structural capture expression from the actual scoped entry. -/
def seedValue : (arg : Tm Empty F n) → Option {seed : Val (Fin n) // erase arg = packetTerm seed}
  | .bv i => some ⟨.var i, rfl⟩
  | .unit => some ⟨.unit, rfl⟩
  | .pair left right => do
    let l ← seedValue left
    let r ← seedValue right
    return ⟨.pair l.val r.val, congrArg₂ LambdaSSA.Tm.pair l.property r.property⟩
  | _ => none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
