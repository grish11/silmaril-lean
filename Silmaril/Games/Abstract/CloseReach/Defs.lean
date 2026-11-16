module

public import Silmaril.Games.Abstract.Module.Defs

/-!
# Closing with reach: callee traps observed without a finished caller

`Shape.close` resolves a callee's trap or divergence only inside a *finished*
open behaviour of the caller that contains the call (`Shape.Subst.intTrap`,
`Shape.Subst.intDiv`). A caller that makes the call but never finishes for any
answer (in Wasm: a loop around a handler catching everything) has no such
behaviour, so the callee's trap is lost.

A **reach relation** (`Shape.ReachRel`) is given next to the open module:
`Rch x u y` reads "a run of the call `x` reaches the internal call `y` after the
open prefix `u`". `closeR m Rch` is the least fixpoint of `resolveR m Rch`,
which is `resolve m` plus, for every reach, the callee's trap or divergence
after the resolved prefix: `(q ++ c₁, .trap)` when `Rch x u y`, `SubstPre c u q`
and `(c₁, .trap)` is a behaviour of `y`; the same for `.div`. These are exactly
the behaviours `Subst.intTrap`/`Subst.intDiv` would give at `y` in a behaviour
of `x` with prefix `u`.

`cutMod m Rch Bad` is the encoding by **cut behaviours**: `m` plus, for each
reach `Rch x u y` and each answer `ans` with `Bad y ans`, the open behaviour
`(u ++ [⟨.inr y, ans⟩], .trap)`. When no closed behaviour returns a `Bad`
answer, the cut call can only be resolved by a trap or divergence of the
callee, and `close (cutMod m Rch Bad) = closeR m Rch`
(`Silmaril.Games.Abstract.CloseReach.Thms`).
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u

namespace Shape

variable (sh : Shape.{u})

/-- A reach relation of an open module of shape `sh`: `Rch x u y` reads "a run
of the call `x` reaches the internal call `y` after the open prefix `u`". -/
abbrev ReachRel : Type u :=
  sh.self.Op → List (Call (sh.E ⊕ₛ sh.self)) → sh.self.Op → Prop

variable {sh}

theorem SubstPre.mono {c c' : sh.ClosedMod} (h : c ≤ c') {x : List (Call (sh.E ⊕ₛ sh.self))}
    {q : List (Call sh.E)} (hs : SubstPre c x q) : SubstPre c' x q := by
  induction hs with
  | nil => exact .nil
  | ext _ ih => exact .ext ih
  | int hc _ ih => exact .int (h _ _ _ hc) ih

/-- The ends added by reach: a run of `x` reaches `z` after the open prefix `u`,
whose internal calls return through `c` with import calls `q`, and `z` traps
(or diverges) in `c` after the import calls `c₁`. -/
def ReachEnd (Rch : sh.ReachRel) (c : sh.ClosedMod) (x : sh.self.Op)
    (y : CallBeh sh.E sh.S (sh.B x.1)) : Prop :=
  ∃ u q z c₁, Rch x u z ∧ SubstPre c u q ∧
    (((c₁, .trap) ∈ c z.1 z.2.2 z.2.1 ∧ y = (q ++ c₁, .trap)) ∨
      ((c₁, .div) ∈ c z.1 z.2.2 z.2.1 ∧ y = (q ++ c₁, .div)))

/-- One round of resolution with reach: `resolve m c`, plus the trap or
divergence of every reached callee after the resolved prefix. -/
def resolveR (m : sh.OpenMod) (Rch : sh.ReachRel) : sh.ClosedMod →o sh.ClosedMod where
  toFun c f s a := resolve m c f s a ∪ {y | ReachEnd Rch c ⟨f, (a, s)⟩ y}
  monotone' _ _ h f s a := Set.union_subset_union ((resolve m).monotone h f s a)
    fun _ ⟨u, q, z, c₁, hr, hq, hz⟩ =>
      ⟨u, q, z, c₁, hr, hq.mono h,
        hz.imp (fun ⟨hm, he⟩ => ⟨h _ _ _ hm, he⟩) (fun ⟨hm, he⟩ => ⟨h _ _ _ hm, he⟩)⟩

/-- Close a module with reach: the least fixpoint of `resolveR`. -/
def closeR (m : sh.OpenMod) (Rch : sh.ReachRel) : sh.ClosedMod := (resolveR m Rch).lfp

/-- The cut module: `m` plus, for every reach `Rch x u y` and every answer `ans`
with `Bad y ans`, the behaviour of `x` that makes the calls `u`, then the call
`y` answered by `ans`, then traps. -/
def cutMod (m : sh.OpenMod) (Rch : sh.ReachRel) (Bad : (y : sh.self.Op) → sh.self.Ar y → Prop) :
    sh.OpenMod := fun f s a =>
  m f s a ∪ {x | ∃ u y ans, Rch ⟨f, (a, s)⟩ u y ∧ Bad y ans ∧ x = (u ++ [⟨.inr y, ans⟩], .trap)}

/-- Every internal call inside a reach prefix is itself reached, or made by a
behaviour of `m` after the same prefix. This is what lets an earlier callee's
trap in a cut behaviour be read as a reach end. -/
def ReachPrefixClosed (m : sh.OpenMod) (Rch : sh.ReachRel) : Prop :=
  ∀ x u y, Rch x u y → ∀ u₁ z ans u₂, u = u₁ ++ ⟨.inr z, ans⟩ :: u₂ →
    Rch x u₁ z ∨ ∃ w ∈ m x.1 x.2.2 x.2.1, ∃ ans' rest, w.1 = u₁ ++ ⟨.inr z, ans'⟩ :: rest

end Shape

end Silmaril.Games.Abstract
