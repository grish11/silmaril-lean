module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Defs

/-! # Recover the actual CF edge packets from the outer-tail Φ view -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op)
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Edge)
open Silmaril.MLIR.Pure (Operands)
open Diamond.MLIR.CF (Label Widths)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {p : Program src entry}
variable {Γ Δ : List Width}

/-- Inspect a successor of the actual CF terminator without a destination test. -/
def successor (slot : Fin 2) :
    Silmaril.MLIR.CF.Terminator (Label regs out size) Δ Γ → Option (Edge (Label regs out size) Γ)
  | .br edge => if slot = 0 then some edge else none
  | .condBr _ yes no => some (if slot = 0 then yes else no)
  | .ret _ => none

/-- A typed de Bruijn position in a CF scope determines a typed CF variable. -/
def lookup {w : Width} : {Γ : List Width} → (i : Nat) →
    Isotope.LambdaSSA.At (Types Γ) i (.base w) → Var Γ w
  | [], i, typed => by cases i <;> cases typed
  | _ :: _, 0, typed => by
    have same : _ = w := Silmaril.Ty.base.inj (Option.some.inj typed)
    cases same
    exact .here
  | _ :: _, i + 1, typed => .there (lookup i typed)

def operands : {Δ : List Width} → PhiView.Arguments (Types Γ) (Types Δ) → Operands Γ Δ
  | [], _ => .nil
  | _ :: _, args =>
    let first := args ⟨0, Nat.zero_lt_succ _⟩
    .cons (lookup first.val first.property) (operands fun i => args i.succ)

/-- Reconstitute the typed CF edge from its actual Φ column, at its original
destination. This is a readback of the existing terminator. -/
def edge (rows : Rows p) (taken : Bool) : Edge (Label regs out size) (Scope p taken) :=
  ⟨.site p.stop, operands ((PhiView.toBlockArgs rows.view (rows.edge taken)).val)⟩

def readBank (rows : Rows p) (taken : Bool) (old : Env (Scope p taken)) : Env (Widths regs) :=
  (edge rows taken).args.eval old

def sameBank : {types : List Width} → Env types → Env types → Bool
  | [], .nil, .nil => true
  | _ :: _, .cons x xs, .cons y ys => (x == y) && sameBank xs ys

/-- Check both candidate full packets in their own original predecessor
environments. The Bool index uses the source outer-true/outer-false order. -/
def checkBanks (rows : Rows p) (old : (taken : Bool) → Env (Scope p taken))
    (proposed : Bool → Env (Widths regs)) : Bool :=
  sameBank (readBank rows true (old true)) (proposed true) &&
    sameBank (readBank rows false (old false)) (proposed false)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback
