module

public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Abstract.RegionCall.Thms
public import Silmaril.Wasm.Cfg.MachineClosed.Defs
import Silmaril.Proofs.Wasm.Cfg.CallClosed
import Silmaril.Proofs.Wasm.Cfg.CallGuard
public import Silmaril.Wasm.Execution.Core.Sim.TypedContext

@[expose] public section

/-!
# The block-CFG machine with the checked closed oracle, against Core 3.0

The machine with calls (`MStepC`) instantiated with the actual oracle `Abstract.closedCallOk`:
calls answered by the closed native semantics (`closedCall`, the least fixpoint of running
callees), restricted to arity-checked stores (`StoreChk`) and typed invocations (`InvokeOk`).
`Abstract.callSoundAnn_closedCallOk` proves it Core-sound (`Region.CallSoundA`) for every profile and
host, so the machine's Core soundness holds with **no oracle hypothesis**:

* **`core_sound_closed`**: a run of the machine with `closedCallOk` from the CFG entry to a sink
  is a Core 3.0 run of the body to a final form of a region outcome the sink completes
  (`EndsC`).

* `callSoundA_closedCallOk`: `closedCallOk` is sound for every `call_ref` annotation
  (`Region.CallSoundA`, from `Abstract.callSoundAnn_closedCallOk`).
* **`frame_tail_closed`**: a run of the machine with `closedCallOk` from the CFG entry that ends
  by a tail call is a Core 3.0 run of the function's `FRAME` to the sink's code (frame
  replacement), with no oracle hypothesis.

* **`callCompleteG_closedCallOk`**: `closedCallOk` is complete for Core calls
  (`Region.CallCompleteG`) on the native slice `NativeCallOk` (typed store, native Wasm functions,
  arity-checked functions, typed invocation), with no host, every profile: every Core run of a
  call, in any caller frame and with any `call_ref` annotation, to a result (values, trap, or
  exception) is answered by it. From `Abstract.closedCall_core_iff` and the host-free transport
  of call runs to `invoke` (`Region.call_transport`). With `Region.call_of_core`, such a Core
  call is a `RunC` call of the machine's oracle.

* **`core_complete_closed`**, **`core_complete_closed_typed`**: Core runs of `FragC` bodies to
  final forms are machine runs with `closedCallOk` (guarded by `NativeCallOk`, discharged from a
  typed native start by `guardedCalls_of_typed`).

* **Divergence.** `closedDiv`: a call on the native slice with no terminating closed-oracle
  entry. `divCallSound_closedDiv`, `divCallComplete_closedDiv`: it is exactly Core divergence of
  the call on the slice, from every caller frame and annotation (`closedCall_none_iff_diverges`
  and the divergent transport `div_call_transport`). **`mdivC_core_closed`**: machine
  divergence `MDivC` with `closedCallOk` and `closedDiv`, from the CFG entry, is Core 3.0
  divergence of the body, no hypothesis. **`core_div_closed`**: conversely, on `FragC` bodies
  whose calls are on the native slice, Core divergence is `MDivC`; **`mdivC_iff_core_closed_typed`**:
  from a typed native start, `MDivC` with the closed oracle is exactly Core divergence.

Not claimed here: host calls (the slice has no host); stores outside `NativeCallOk`; extended
calls (`call_ref`, `call_indirect`) in block bodies.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {body : Expr}

/-- The checked closed oracle is Core-sound for every `call_ref` annotation. -/
theorem callSoundA_closedCallOk (P : Profile) (host : HostSemantics H) :
    Region.CallSoundA P host (Abstract.closedCallOk (H := H)) :=
  fun s s₁ f a fi ps rs us fl c hc hfi hty hn hcall =>
    Abstract.callSoundAnn_closedCallOk P host s s₁ f a fi ps rs us fl c hc hfi hty hn hcall

/-- **Core soundness of the machine with the checked closed oracle**, every profile and host,
no oracle hypothesis: a run from the CFG entry to a sink is a Core 3.0 run of the body to a final
form of the region outcome the sink completes. -/
theorem core_sound_closed {s : Store H} {f : Frame} {st' : MState H}
    (h : Relation.ReflTransGen (MStepC P host Abstract.closedCallOk body) (initial body s f) st')
    (hs : st'.node.IsSink) :
    ∃ o s₂ f₂ c', EndsC Abstract.closedCallOk st' s₂ f₂ o ∧
      Steps P host ⟨s, f, expression body⟩ ⟨s₂, f₂, c'⟩ ∧ o.Ends c' :=
  core_sound_initialC (callSoundA_closedCallOk P host) h hs

/-- **Tail calls at the frame with the checked closed oracle**, no oracle hypothesis: a run from
the CFG entry ending by a tail call is a Core 3.0 run of `FRAME_n{fi} (LABEL_n{} body)`, in any
outer frame, to the code of the sink the machine reached. -/
theorem frame_tail_closed {s : Store H} {fi : Frame} {st' : MState H} {s₂ : Store H}
    {f₂ : Frame} {W : List Val} {a : Nat} {c : Admin}
    (hE : EndsC Abstract.closedCallOk st' s₂ f₂ (.tail W a c))
    (hR : Region.RunC P host Abstract.closedCallOk s fi [] (expression body) s₂ f₂ (.tail W a c))
    (n : Nat) (f : Frame) {X : List Admin} (hX : codeOf body st' = some X) :
    Steps P host ⟨s, f, [.frame n fi [.label n [] (expression body)]]⟩ ⟨st'.store, f, X⟩ :=
  frame_tail_initialC (callSoundA_closedCallOk P host) hE hR n f hX

/-- **The checked closed oracle is complete for Core calls on the native slice**, every profile,
no host. -/
theorem callCompleteG_closedCallOk (P : Profile) :
    Region.CallCompleteG P (fun _ _ _ _ => False) NativeCallOk (Abstract.closedCallOk (H := H)) :=
  Proofs.Region.callCompleteG_closedCallOk P

/-- **Core completeness of the machine with the checked closed oracle** (native direct-call
slice, no host, every profile): a Core 3.0 run of a function body of the fragment with direct
calls (`FragC`) to a final form of `o` (not a branch out of the body, not a tail call of a
function) is a run of the machine with `closedCallOk` from the CFG entry to a sink ending as
`Ends` says, in the same store and frame, provided every call the run reaches is on the native
slice (`GuardedCalls … NativeCallOk`: typed store, native Wasm functions, arity-checked
functions, typed invocation). -/
theorem core_complete_closed (P : Profile) {s s' : Store H} {f f' : Frame} {c' : List Admin}
    {o : Region.Out} (hF : Region.FragC (expression body))
    (hG : Region.GuardedCalls P (fun _ _ _ _ => False) NativeCallOk ⟨s, f, expression body⟩)
    (h : Steps P (fun _ _ _ _ => False) ⟨s, f, expression body⟩ ⟨s', f', c'⟩) (he : o.Ends c')
    (ho : ∀ k us, o ≠ .br k us) (hto : ∀ W a c, o ≠ .tail W a c) :
    ∃ st', Relation.ReflTransGen (MStepC P (fun _ _ _ _ => False) Abstract.closedCallOk body)
        (initial body s f) st' ∧ Ends st' o ∧ st'.store = s' ∧ st'.frame = f' :=
  run_complete_initialC (Region.run_completeC (callCompleteG_closedCallOk P) hG hF h he) ho hto

/-- **The native-slice guard from typing** (no host, every profile): from a typed start
(`ContextTyped`) on a store of native, arity-checked functions, every call a host-free run
reaches is on the native slice (`NativeCallOk`). The store stays typed, the functions are
unchanged, and each call's arguments are a typed invocation (the typed `call_ref` it resolves to
types them at the callee's parameters, `PC.callRef_front`). -/
theorem guardedCalls_of_typed {P : Profile} {c₀ : Config H} (hT : Sim.ContextTyped c₀)
    (hN : Binaryen.NativeFuncsOk c₀.store.funcs) (hS : Interp.StoreChk c₀.store.funcs) :
    Region.GuardedCalls P (fun _ _ _ _ => False) NativeCallOk c₀ :=
  Proofs.Region.guardedCalls_of_typed hT hN hS

/-- **Core completeness of the machine with the checked closed oracle, from a typed native
start** (no host, every profile, no oracle or guard hypothesis): a Core 3.0 run of a typed
(`ContextTyped`) function body of the fragment with direct calls (`FragC`), on a store of native,
arity-checked functions, to a final form of `o` (not a branch out of the body, not a tail call of
a function) is a run of the machine with `closedCallOk` from the CFG entry to a sink ending as
`Ends` says, in the same store and frame. -/
theorem core_complete_closed_typed (P : Profile) {s s' : Store H} {f f' : Frame}
    {c' : List Admin} {o : Region.Out} (hF : Region.FragC (expression body))
    (hT : Sim.ContextTyped ⟨s, f, expression body⟩) (hN : Binaryen.NativeFuncsOk s.funcs)
    (hS : Interp.StoreChk s.funcs)
    (h : Steps P (fun _ _ _ _ => False) ⟨s, f, expression body⟩ ⟨s', f', c'⟩) (he : o.Ends c')
    (ho : ∀ k us, o ≠ .br k us) (hto : ∀ W a c, o ≠ .tail W a c) :
    ∃ st', Relation.ReflTransGen (MStepC P (fun _ _ _ _ => False) Abstract.closedCallOk body)
        (initial body s f) st' ∧ Ends st' o ∧ st'.store = s' ∧ st'.frame = f' :=
  core_complete_closed P hF (guardedCalls_of_typed hT hN hS) h he ho hto

/-! ## Divergence -/

/-- **The checked closed divergence predicate is Core-sound** (no host, every profile): a call on
the native slice with no terminating closed-oracle entry diverges in Core, from every caller
frame and with every `call_ref` annotation. -/
theorem divCallSound_closedDiv (P : Profile) :
    Region.DivCallSound P (fun _ _ _ _ => False) (closedDiv (H := H)) :=
  Proofs.Region.divCallSound_closedDiv P

/-- **The checked closed divergence predicate is complete for Core on the native slice** (no
host, every profile): a call on the slice that diverges in Core satisfies `closedDiv`. -/
theorem divCallComplete_closedDiv (P : Profile) :
    Region.DivCallComplete P (fun _ _ _ _ => False) NativeCallOk (closedDiv (H := H)) :=
  Proofs.Region.divCallComplete_closedDiv P

/-- **Soundness of machine divergence with the checked closed oracle** (no host, every profile,
no oracle hypothesis): `MDivC` with `closedCallOk` answering terminating calls and `closedDiv`
naming diverging ones, from the CFG entry, is Core 3.0 divergence of the body. -/
theorem mdivC_core_closed (P : Profile) {s : Store H} {f : Frame}
    (h : MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv body (initial body s f)) :
    Diverges P (fun _ _ _ _ => False) ⟨s, f, expression body⟩ :=
  mdivC_core_initial (callSoundA_closedCallOk P _) (divCallSound_closedDiv P) h

/-- **Completeness of machine divergence with the checked closed oracle** (no host, every
profile, no oracle hypothesis): a diverging Core 3.0 run of a body of the fragment with direct
calls (`FragC`) is `MDivC` with `closedCallOk` and `closedDiv` from the CFG entry, provided every
call the run reaches is on the native slice. -/
theorem core_div_closed (P : Profile) {s : Store H} {f : Frame}
    (hF : Region.FragC (expression body))
    (hG : Region.GuardedCalls P (fun _ _ _ _ => False) NativeCallOk ⟨s, f, expression body⟩)
    (h : Diverges P (fun _ _ _ _ => False) ⟨s, f, expression body⟩) :
    MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv body (initial body s f) :=
  core_div_initialC (callCompleteG_closedCallOk P) (divCallComplete_closedDiv P) hF hG h

/-- **Divergence adequacy of the machine with the checked closed oracle, from a typed native
start** (no host, every profile, no oracle or guard hypothesis): on a typed (`ContextTyped`)
body of the fragment with direct calls (`FragC`), over a store of native, arity-checked
functions, machine divergence `MDivC` with `closedCallOk` and `closedDiv` from the CFG entry is
exactly Core 3.0 divergence of the body, divergence inside a callee included. -/
theorem mdivC_iff_core_closed_typed (P : Profile) {s : Store H} {f : Frame}
    (hF : Region.FragC (expression body)) (hT : Sim.ContextTyped ⟨s, f, expression body⟩)
    (hN : Binaryen.NativeFuncsOk s.funcs) (hS : Interp.StoreChk s.funcs) :
    MDivC P (fun _ _ _ _ => False) Abstract.closedCallOk closedDiv body (initial body s f) ↔
      Diverges P (fun _ _ _ _ => False) ⟨s, f, expression body⟩ :=
  ⟨mdivC_core_closed P, core_div_closed P hF (guardedCalls_of_typed hT hN hS)⟩

end Silmaril.Wasm.Cfg.Machine
