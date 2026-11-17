module

public import Silmaril.Wasm.Cfg.DanglingTyped.Defs
public import Silmaril.Wasm.Abstract.HostCall.Defs
public import Silmaril.Wasm.Cfg.CfgInst.Defs
public import Silmaril.Wasm.Cfg.CfgInst.Thms
import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Init
import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Chk

@[expose] public section

/-!
# A relaxed typing invariant for dangling exception references: theorems

**Preservation.** `ConfigOkD` (definitions in `Silmaril.Wasm.Cfg.DanglingTyped.Defs`) is kept by
Core reduction at every numeric profile, and by host answers that keep the store and type their
values, whatever exception address they throw:

* `ConfigOkD.step`, `ConfigOkD.steps`: host-free Core steps and runs. A step that keeps the
  exceptions is matched by a step of the same code on the witness store, since every decision it
  takes reads the same answer there (`catchMatches_gst_iff`: a pad's tag is no frame's tag;
  `refOk_gst_iff`: supported casts never accept an exception reference), and Core preservation
  types the result on the witness; a caught payload is read from the witness and differs from the
  actual one only in exception addresses. A Wasm `throw` allocates at `s.exns.length` in the actual
  store but at `X.length` on the witness: the new witness moves the allocated exception to its
  actual address, the pad to the end, and redirects every exception field to that pad, which
  rules out the cycles that aliasing creates (`DanglingExn.not_storeOk_addExn_self`);
* `ConfigOkD.event`: one answered host call, the witness first padded to name the thrown address;
* `ConfigOkD.evRun`: labelled Core runs (`Abstract.EvRun`) against a host in `HostTypedD`;
  `hostTypedD_instHostU`: the unrestricted universal host of an instance is one.

**Entry and exit.** `storeOkD_of_storeOk`: a `StoreOk` store with supported functions satisfies
`StoreOkD`. `configOkD_invoke`: an invocation typed on a witness satisfies `ConfigOkD`.
`storeOkD_of_configOkD`: the store of every reached configuration satisfies `StoreOkD`; so the end
store of a round does, though it need not be `StoreOk`.

**The checker's profile is supported.** `funcsSupp_of_storeSupported`: a `StoreOk` store whose
Wasm functions are in the checker's instruction profile (`CheckComplete.StoreSupported`, decided
by `storeSupportedB`) has supported functions (`FuncsSupp`): `XProfile.xInstr` has no
`ref.test`, `ref.cast`, `br_on_cast*` or aggregate instruction. `configOkD_invoke_of_storeOk`,
`configOkD_of_supported`: every export question of a well-formed instance store in that profile
(hence in `CfgInst.InstDom`, `CfgInst.instDom_of_supported`) enters `ConfigOkD`. Checker
acceptance alone (`StoreChkE`, so `InstDom`) does **not** give `FuncsSupp`: the checker skips
code after an instruction that never falls through, which may hold an unsupported instruction
(`ExampleAlias.dc_instDom`, `dc_not_funcsSupp`).

**Not claimed here.** No theorem here relates Core and the native/CFG semantics. The backward
simulation (`Abstract.HostClosingXP`, `HostClosingInfXPBack`, `HostEval`) is still stated for
`Sim.ContextTyped` configurations and `HostTyped` hosts; carrying it over `ConfigOkD` is open.
The supported profile excludes `ref.test`, `br_on_cast*`, aggregates and abstract-heap
`ref.cast`, where Core's decision on a dangling reference (`DanglingExn.step_refTest`,
`step_refCast`) differs from the witness's.
-/

namespace Silmaril.Wasm.Cfg.DanglingTyped

open Silmaril.Games.Abstract (Call)
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type} {P : Numerics.Profile}

/-! ## Decisions on the witness -/

/-- **A catch clause decides alike on a store and its witness**, at a frame below its tags. -/
theorem catchMatches_gst_iff {s : Store H} {T : List TagInst} {X : List ExnInst}
    (hg : GhostOk s T X) {f : Frame} (hf : FrameBelow s.tags.length f) {a : Nat} {c : Catch} :
    CatchMatches (gst s T X) f a c ↔ CatchMatches s f a c :=
  Proofs.DanglingTyped.catchMatches_gst_iff hg hf

/-- **A supported cast decides alike on a store and its witness.** -/
theorem refOk_gst_iff {s : Store H} {T : List TagInst} {X : List ExnInst} (hg : GhostOk s T X)
    {m : ModuleInst} {r : Ref} {rt : RefType} (hn : ¬ Unsupp (.refCast rt)) :
    RefOk (gst s T X) r (m.instRef rt) ↔ RefOk s r (m.instRef rt) :=
  Proofs.DanglingTyped.refOk_gst_iff hg hn

/-- An exception reference is never a reference to a defined type. -/
theorem not_refOk_exn_typeIdx {s : Store H} {m : ModuleInst} {a : Nat} {b : Bool} {y : TypeIdx} :
    ¬ RefOk s (.exn a) (m.instRef ⟨b, .typeIdx y⟩) :=
  Proofs.DanglingTyped.not_refOk_exn_typeIdx

/-! ## Preservation -/

/-- **A host-free Core step keeps the relaxed invariant** (every numeric profile). -/
theorem ConfigOkD.step {c c' : Config H} (hc : ConfigOkD c)
    (h : Step P (fun _ _ _ _ => False) c c') : ConfigOkD c' :=
  Proofs.DanglingTyped.ConfigOkD.step hc h

theorem ConfigOkD.steps {c c' : Config H} (hc : ConfigOkD c)
    (h : Steps P (fun _ _ _ _ => False) c c') : ConfigOkD c' :=
  Proofs.DanglingTyped.ConfigOkD.steps hc h

/-- **An answered host call keeps the relaxed invariant** when the answer keeps the store and
types its values, whatever exception address it throws. -/
theorem ConfigOkD.event {host : HostSemantics H} {c c' : Config H}
    {e : Call (Abstract.wasmHostSig H)} (hc : ConfigOkD c) (h : Abstract.HEvStep P host c (some e) c')
    (hsp : e.2.1 = e.1.2.1)
    (hres : ∀ fi ∈ c.store.funcs, fi.code = .host e.1.1 → ∀ ps rs,
      Expand fi.type (.func ps rs) → ResultTypedD c.store e.2.2 rs.toList) :
    ConfigOkD c' :=
  Proofs.DanglingTyped.ConfigOkD.event hc h hsp hres

/-- **Labelled runs keep the relaxed invariant**, against a store-keeping host with typed values. -/
theorem ConfigOkD.evRun {host : HostSemantics H} (hT : HostTypedD host) {c c' : Config H}
    {cs : List (Call (Abstract.wasmHostSig H))} (hc : ConfigOkD c)
    (h : Abstract.EvRun P host c cs c') : ConfigOkD c' :=
  Proofs.DanglingTyped.ConfigOkD.evRun hT hc h

/-- Every restricted universal host of an instance keeps the store and types its values. -/
theorem hostTypedD_instHostQ {I : Game.ScalarInstance} {Q : Store Nat → Result → Prop} :
    HostTypedD (CfgInst.instHostQ I Q) :=
  Proofs.DanglingTyped.hostTypedD_instHostQ

/-- **The unrestricted universal host of an instance** (dangling exceptions included). -/
theorem hostTypedD_instHostU {I : Game.ScalarInstance} : HostTypedD (CfgInst.instHostU I) :=
  Proofs.DanglingTyped.hostTypedD_instHostU

/-! ## Entry and exit -/

/-- The store of a configuration in the relaxed invariant satisfies the relaxed store invariant. -/
theorem storeOkD_of_configOkD {c : Config H} (h : ConfigOkD c) : StoreOkD c.store :=
  Proofs.DanglingTyped.storeOkD_of_configOkD h

/-- **A typed store with supported functions satisfies the relaxed store invariant.** -/
theorem storeOkD_of_storeOk {s : Store H} (hs : StoreOk s) (hF : FuncsSupp s) : StoreOkD s :=
  Proofs.DanglingTyped.storeOkD_of_storeOk hs hF

/-- **An invocation typed on a witness enters the relaxed invariant.** -/
theorem configOkD_invoke {s : Store H} {T : List TagInst} {X : List ExnInst} (hF : FuncsSupp s)
    (hheap : HeapBelow s) (hg : GhostOk s T X) (hS : StoreOk (gst s T X)) {a : Nat}
    {vs : List Val} (hok : InvokeOk (gst s T X) a vs) : ConfigOkD (invoke s a vs) :=
  Proofs.DanglingTyped.configOkD_invoke hF hheap hg hS hok

/-! ## The checker's profile -/

/-- **A typed store whose Wasm functions are in the checker's instruction profile has supported
functions.** -/
theorem funcsSupp_of_storeSupported {s : Store H} (hs : StoreOk s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) : FuncsSupp s :=
  Proofs.DanglingTyped.funcsSupp_of_storeSupported hs hsup

/-- **A typed invocation in a typed store with supported functions enters the relaxed
invariant.** -/
theorem configOkD_invoke_of_storeOk {s : Store H} (hs : StoreOk s) (hF : FuncsSupp s) {a : Nat}
    {vs : List Val} (hok : InvokeOk s a vs) : ConfigOkD (invoke s a vs) :=
  Proofs.DanglingTyped.configOkD_invoke_of_storeOk hs hF hok

/-- **Every export question of a well-formed instance store in the checker's profile enters the
relaxed invariant.** -/
theorem configOkD_of_supported {I : Game.ScalarInstance} {s : Store Nat} (hw : I.WellFormed s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) (a : I.F.Op) :
    ConfigOkD (invoke s (Abstract.NodeBridge.qOf I a).1 (Abstract.NodeBridge.qOf I a).2) :=
  configOkD_invoke_of_storeOk hw.storeOk (funcsSupp_of_storeSupported hw.storeOk hsup)
    (CfgInst.invOkXP_of_dom (CfgInst.instDom_of_supported hw hsup) a).2.2.2

end Silmaril.Wasm.Cfg.DanglingTyped
