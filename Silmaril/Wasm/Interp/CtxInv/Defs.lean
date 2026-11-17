module

public import Silmaril.Wasm.Execution.Core.Sim.TypedContext
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
public import Silmaril.Wasm.SingleThreaded.Profile

@[expose] public section

/-!
# Invariants for the backward simulations: the interface (definitions)

The backward simulations between Core and the native/CFG semantics (`Abstract.HostClosingXP`,
`Abstract.HostClosingInfXPBack`) and the native progress lemmas of `Interp` (`TypedP`,
`evalDivXP_of_noOutcome`) carry an invariant of Core configurations. Originally that invariant
is `Sim.ContextTyped` (the fragment sits in a typed whole configuration, on the actual store)
against hosts with typed answers (`Abstract.HostTyped`). The proofs use only the following
consequences of it, collected here so that each lemma is proved once, for every invariant with
these operations:

* `CtxInv H`: an invariant `CT` of configurations with
  - the context decompositions `suffix`, `label`, `handler`, `frame` (the hole of an active
    context);
  - preservation under host-free Core steps at every numeric profile (`step`);
  - a **typing witness** (`wit`): the same frame and code are typed in context
    (`Sim.ContextTyped`) on the store with other tags `T` (extending the store's) and other
    exception instances `X`, every other component unchanged, and the defined-type casts that
    `call_indirect` performs (`RefOk` at `m.instRef ⟨b, .typeIdx y⟩`) decide alike on both
    stores. Every native-progress fact the simulations read off typing (stack shapes at a site,
    function types, indirect-call resolution, `evalFlat` progress) is a fact of the witness that
    does not read tags or exception instances, so it transfers to the actual store. Nothing else
    is read from the witness: no operational step is taken on it;
* `BackInv H`, a `CtxInv` with a class of hosts `HostOk`:
  - preservation along Core runs of a host in `HostOk` (`steps_host`), the class closed under
    answering one call by a trap in its store (`hostOk_trap`);
  - **host-free divergence passes through every host-free step** of a configuration in the
    invariant, in the deterministic profile (`through`). This is about Core runs on the actual
    store, so it is not read off the witness.

Instances: the typed setting (`Sim.ContextTyped`, `HostTyped`; `Interp.ctxTyped`,
`Abstract.HostClosingXP.backTyped`) and the relaxed setting for dangling host exceptions
(`Cfg.DanglingTyped.ConfigOkD`, `HostTypedD`).
-/

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- **The configuration invariant of the native progress lemmas.** -/
structure CtxInv (H : Type) where
  /-- The invariant. -/
  CT : Config H → Prop
  suffix : ∀ {s : Store H} {f : Frame} {body rest : List Admin},
    CT ⟨s, f, body ++ rest⟩ → CT ⟨s, f, body⟩
  label : ∀ {s : Store H} {f : Frame} {n : Nat} {cont : List Instr} {vs : List Val}
    {body rest : List Admin}, CT ⟨s, f, vals vs ++ [.label n cont body] ++ rest⟩ → CT ⟨s, f, body⟩
  handler : ∀ {s : Store H} {f : Frame} {n : Nat} {cs : List Catch} {vs : List Val}
    {body rest : List Admin}, CT ⟨s, f, vals vs ++ [.handler n cs body] ++ rest⟩ →
      CT ⟨s, f, body⟩
  frame : ∀ {s : Store H} {f fi : Frame} {n : Nat} {vs : List Val} {body rest : List Admin},
    CT ⟨s, f, vals vs ++ [.frame n fi body] ++ rest⟩ → CT ⟨s, fi, body⟩
  step : ∀ {P : Numerics.Profile} {c c' : Config H}, CT c →
    Step P (fun _ _ _ _ => False) c c' → CT c'
  wit : ∀ {c : Config H}, CT c → ∃ (T : List TagInst) (X : List ExnInst), c.store.tags <+: T ∧
    (∀ (m : ModuleInst) (r : Ref) (b : Bool) (y : TypeIdx),
      RefOk { c.store with tags := T, exns := X } r (m.instRef ⟨b, .typeIdx y⟩) ↔
        RefOk c.store r (m.instRef ⟨b, .typeIdx y⟩)) ∧
    Sim.ContextTyped ⟨{ c.store with tags := T, exns := X }, c.frame, c.code⟩

/-- **The typed instance**: `Sim.ContextTyped` is its own witness (tags and exception instances
unchanged). -/
def ctxTyped : CtxInv H where
  CT := Sim.ContextTyped
  suffix h := Sim.ContextTyped.suffix h
  label h := Sim.ContextTyped.label h
  handler h := Sim.ContextTyped.handler h
  frame h := Sim.ContextTyped.frame h
  step h hs := Sim.ContextTyped.step h hs
  wit {c} h := ⟨c.store.tags, c.store.exns, List.prefix_refl _, fun _ _ _ _ => Iff.rfl, h⟩

/-- `host`, also answering the call `(h, s, vs)` by a trap in its store `s`. -/
def trapAt (host : HostSemantics H) (m : H × Store H × List Val) : HostSemantics H :=
  fun h s vs o => host h s vs o ∨ (h = m.1 ∧ s = m.2.1 ∧ vs = m.2.2 ∧ o = .returned m.2.1 .trap)

/-- **The invariant of the backward simulations**: a `CtxInv` with a class of hosts along whose
runs it is kept, and through which host-free divergence passes host-free steps. -/
structure BackInv (H : Type) extends CtxInv H where
  /-- The hosts. -/
  HostOk : HostSemantics H → Prop
  steps_host : ∀ {P : Numerics.Profile} {host : HostSemantics H} {c c' : Config H},
    HostOk host → CT c → Steps P host c c' → CT c'
  hostOk_trap : ∀ {host : HostSemantics H} (m : H × Store H × List Val),
    HostOk host → HostOk (trapAt host m)
  through : ∀ {o : GrowOracle} {host : HostSemantics H} {K d : Config H}, CT K →
    Diverges (profile o) host K → Det.DStep o K d → Diverges (profile o) host d

end Silmaril.Wasm.Interp
