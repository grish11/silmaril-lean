module

public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Abstract.RegionCall.Thms
public import Silmaril.Wasm.Cfg.MachineClosed.Defs
import Silmaril.Proofs.Wasm.Cfg.CallClosed

@[expose] public section

/-!
# The block-CFG machine with the checked closed oracle, against Core 3.0

The machine with calls (`MStepC`) instantiated with the actual oracle `Abstract.closedCallOk`:
calls answered by the closed native semantics (`closedCall`, the least fixpoint of running
callees), restricted to arity-checked stores (`StoreChk`) and typed invocations (`InvokeOk`).
`Abstract.callSound_closedCallOk` proves it Core-sound (`Region.CallSound`) for every profile and
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

Not claimed here: Core completeness of whole bodies with calls (Core runs to `RunC`): it needs the
decomposition of a Core run of a body around each call's frame, coordinated on #207; host calls
(the slice has no host); stores outside `NativeCallOk`.
-/

namespace Silmaril.Wasm.Cfg.Machine

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {body : Expr}

/-- **Core soundness of the machine with the checked closed oracle**, every profile and host,
no oracle hypothesis: a run from the CFG entry to a sink is a Core 3.0 run of the body to a final
form of the region outcome the sink completes. -/
theorem core_sound_closed {s : Store H} {f : Frame} {st' : MState H}
    (h : Relation.ReflTransGen (MStepC P host Abstract.closedCallOk body) (initial body s f) st')
    (hs : st'.node.IsSink) :
    ∃ o s₂ f₂ c', EndsC Abstract.closedCallOk st' s₂ f₂ o ∧
      Steps P host ⟨s, f, expression body⟩ ⟨s₂, f₂, c'⟩ ∧ o.Ends c' :=
  core_sound_initialC (Abstract.callSound_closedCallOk P host) h hs

/-- The checked closed oracle is Core-sound for every `call_ref` annotation. -/
theorem callSoundA_closedCallOk (P : Profile) (host : HostSemantics H) :
    Region.CallSoundA P host (Abstract.closedCallOk (H := H)) :=
  fun s s₁ f a fi ps rs us fl c hc hfi hty hn hcall =>
    Abstract.callSoundAnn_closedCallOk P host s s₁ f a fi ps rs us fl c hc hfi hty hn hcall

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

end Silmaril.Wasm.Cfg.Machine
