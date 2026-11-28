module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Thms

/-! # A single directed entry-let rewrite in a written region -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet

open Silmaril.DeBruijn (lift)

/-- An address in a region. Addresses only descend through region
constructors, leaving term operands intact. -/
inductive Site where
  | here
  | unaryBody (next : Site)
  | binaryBody (next : Site)
  | leftArm (next : Site)
  | rightArm (next : Site)
  | entry (next : Site)
  | block (index : Nat) (next : Site)

/-- Apply a partial region rewrite at one address. -/
def Site.rewriteAt {Φ : Type v} (action : Region Φ → Option (Region Φ)) :
    Site → Region Φ → Option (Region Φ)
  | .here, r => action r
  | .unaryBody next, .let₁ a body => (next.rewriteAt action body).map (.let₁ a)
  | .binaryBody next, .let₂ a body => (next.rewriteAt action body).map (.let₂ a)
  | .leftArm next, .case a left right => (next.rewriteAt action left).map (fun l => .case a l right)
  | .rightArm next, .case a left right => (next.rewriteAt action right).map (.case a left)
  | .entry next, .cfg body n blocks => (next.rewriteAt action body).map (fun e => .cfg e n blocks)
  | .block i next, .cfg body n blocks =>
    if hi : i < n then
      (next.rewriteAt action (blocks ⟨i, hi⟩)).map (fun b => .cfg body n (Function.update blocks ⟨i, hi⟩ b))
    else none
  | _, _ => none

/-- Move a unary let out of the CFG at the root. -/
def Site.moveEntry {Φ : Type v} : Region Φ → Option (Region Φ)
  | .cfg (.let₁ a body) n blocks =>
    some (.let₁ a (.cfg body n (fun i => (blocks i).renameVars (lift Nat.succ))))
  | _ => none

/-- Move a unary entry let at one addressed CFG. -/
abbrev Site.move {Φ : Type v} (site : Site) (r : Region Φ) : Option (Region Φ) :=
  site.rewriteAt Site.moveEntry r

/-- Apply the sites in order. Each address is relative to the region
produced by the previous move. -/
def Site.moveAll {Φ : Type v} (sites : List Site) (r : Region Φ) : Option (Region Φ) :=
  sites.foldlM (fun body site => site.move body) r

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet
