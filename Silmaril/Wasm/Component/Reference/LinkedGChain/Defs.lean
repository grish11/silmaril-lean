module

public import Silmaril.Wasm.Component.Reference.LinkedGInst.Defs

/-!
# Chains of linked components on the reference side: definitions

**Scope.** The reference side of chains (`LinkedN`, `chainExp` of `LinkedG`): a linked
component, as an exporter (`LinkedG.toExp`), meets the reference interface `ExpSpec.RefAdeqUX`
of `LinkedGInst` (R1, R2, R3 as `BwdF`, R4 as `InitUX`, R5, R6); `Thms` proves it
(`LinkedG.toExp_refAdeqUX`) and derives chain adequacy.

* `LinkedG.LinkOk`: the hypotheses of `LinkedG.sessAdequacy_fullUX` on the importer and its
  wiring (`WireTy`, an injective wiring, `Good`, `Inst`, within the flat arities, float-free, in
  the split fragment, export names that are not generated type names);
* `ChainOkR e bs Is`: `LinkOk` for each link of the chain built on `e`, with the importer's core
  instance (the reference counterpart of `ChainOk`).

Why `RefAdeqUX` and not `RefAdeqU`: a linked exporter's core store holds its importer's
trampolines (host functions), which `RefAdeqU`'s R4 excludes (`InitAt.hostFree`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Reference

open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)

/-- **The hypotheses on a link's importer and wiring** used by `LinkedG.sessAdequacy_fullUX`. -/
structure LinkedG.LinkOk (lg : LinkedG) : Prop where
  wireTy : lg.WireTy
  nodup : lg.wire.Nodup
  good : lg.imp.Good
  inst : lg.imp.Inst
  arity : lg.imp.Arity
  floats : lg.imp.FloatFree
  split : Linked2.ModSplitOk lg.imp.mod.mod
  names : ∀ x ∈ lg.imp.exports, ∀ n, x.name ≠ tag "t" n

/-- **The reference hypotheses of the links of a chain** built on `e`: `LinkOk` for each link,
`I` an instance of its importer's core module; one instance per importer. -/
def ChainOkR : ExpSpec → List (SimpleI × List Nat) → List ScalarInstance → Prop
  | _, [], [] => True
  | e, (b, w) :: bs, I :: Is =>
    (LinkedG.mk e b w).LinkOk ∧ b.mod.IsInst I ∧ ChainOkR (LinkedG.toExp ⟨e, b, w⟩ I) bs Is
  | _, _, _ => False

end Silmaril.Wasm.Component.Reference
