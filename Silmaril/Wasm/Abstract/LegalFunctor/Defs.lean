module

public import Silmaril.Wasm.Abstract.WorldFunctor.Defs

/-!
# The typed premonoidal Elgot functor over legal oracles (definitions)

#572's `TypedFunctor.exists_not_whisker` refutes the whiskering equation for checked
`call 0; drop` (callee `[] → [i32]`) with an oracle answer carrying **no values**, an answer
short of the callee's declared results. The exit monad `PX H` quantifies over every answer
`Store H × Flow`, legal or not. #579's `WorldFunctor.worldElgot` keeps whiskering for all checked
code, but answers every call by the one oracle `closedCallXP`. This topic changes the codomain
to quantify over **legal** oracles only.

**Legal oracles.** `Legal Γ C` is `ArityResp Γ (fitP C)`. Restricted to calls passing the
callee's parameter count, `C`'s answers keep the store agreeing with the world `Γ` (functions and
tag invariants) and return at least the callee's declared result count. This is all the laws
below use, and it is weaker than `ArityResp Γ C`. It is implied by `ArityResp Γ C` and by typed
answers (`TypedCat.TypedAns`), and the closure `closedCallXP` satisfies it
(`TypedCat.arityResp_fitClosed`). Checked code makes fitting calls only (`TypedCatFit`), so the
result invariant and the answered stack tensor need nothing more. "Legal" means callee-arity
respecting, within the world; it does not ask the answered values to be well typed.

**The codomain.** `LObj Γ`: the objects of #579's `RObj Γ` (typed interfaces with valid stack
types, coherent with the world). `LHom Γ I J`: families, indexed by legal oracles, of #579's
`RHom Γ I J`. Each member is a relation of answered runs supported on the world states of `I`,
landing in those of `J`, and trap-closed.

**The operational equivalence.** `OpEquivL Γ I es es'`: for every legal oracle `C` and every
world state `(s, f, stk)` of `I`, the `EvalOXP C` runs of `es` and `es'` reach the same
non-trap outcomes (store, frame and result), and one traps exactly when the other does (a trap's
store and frame are forgotten). This is stated with runs, not with denotations.

**The quotient domain.** `LDom Γ`: the same objects. Its morphisms (`LegalFunctor.Thms`) are
typed checked code modulo `OpEquivL`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.LegalFunctor

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.TypedCat Silmaril.Wasm.Abstract.WorldFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)

variable {H : Type}

/-- **A legal oracle** for the world `Γ`: on calls passing the callee's parameter count, its
answers keep agreeing with `Γ` and return at least the callee's declared result count. -/
def Legal (Γ : Ctx H) (C : Abstract.CallRel H) : Prop := ArityResp Γ (fitP C)

/-- The objects of the codomain: those of #579's `RObj Γ`. -/
def LObj (Γ : Ctx H) : Type := {I : TIface // I.Ok ∧ Coh Γ I}

/-- **The morphisms of the codomain**: a morphism of #579's `RObj Γ` for every legal oracle. -/
abbrev LHom (Γ : Ctx H) (I J : TIface) : Type :=
  (C : Abstract.CallRel H) → Legal Γ C → RHom Γ I J

/-- **The operational equivalence over legal oracles** at the interface `I`: at every world state
of `I`, under every legal oracle, the same `EvalOXP` runs up to a trap's store and frame. -/
def OpEquivL (Γ : Ctx H) (I : TIface) (es es' : List BExpr) : Prop :=
  ∀ C : Abstract.CallRel H, Legal Γ C → ∀ s f stk, WSt Γ I s f stk →
    (∀ s' f' (o : POut), o ≠ .flow .trap →
      (EvalOXP C s f stk es (s', f', o) ↔ EvalOXP C s f stk es' (s', f', o))) ∧
    ((∃ s' f', EvalOXP C s f stk es (s', f', .flow .trap)) ↔
      ∃ s' f', EvalOXP C s f stk es' (s', f', .flow .trap))

/-- The objects of the domain modulo `OpEquivL`. -/
def LDom (Γ : Ctx H) : Type := {I : TIface // I.Ok ∧ Coh Γ I}

end Silmaril.Wasm.Abstract.LegalFunctor
