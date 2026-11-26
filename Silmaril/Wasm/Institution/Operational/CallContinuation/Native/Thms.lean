module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Thms
public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Lime1Head
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation

open Execution
open Execution.Runtime (Frame FuncAddr Value)
open Wasm.SingleThreaded.Det (noHost)

section v1
variable {H : Type} {s : Wasm.V1.Execution.Store H}
  {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}

theorem v1_sound (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a b : State} (edge : Edge fn a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller addr fn a) (v1Config s caller addr fn b) :=
  Proofs.V1.sound allocated edge

theorem v1_step_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {b : Wasm.V1.Execution.Config H} (guard : Admitted fn a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller addr fn a) b ↔
      ∃ out, Edge fn a out ∧ b = v1Config s caller addr fn out :=
  ⟨Proofs.V1.readback allocated guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound allocated edge⟩

theorem v1_run_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.v1Func))
    {a : State} {b : Wasm.V1.Execution.Config H} (guard : Admitted fn a) :
    Relation.ReflTransGen (Wasm.V1.Execution.Step CallFrame.v1NoHost) (v1Config s caller addr fn a) b ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ b = v1Config s caller addr fn out :=
  Proofs.run_iff (v1Config s caller addr fn) _ (fun e => v1_sound allocated e)
    (fun h step => (v1_step_iff allocated h).mp step) guard

end v1

section lime
variable {H : Type} {s : Wasm.Lime1.Execution.Store H}
  {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}

theorem lime_sound (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a b : State} (edge : Edge fn a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller addr fn a) (limeConfig s caller addr fn b) :=
  Proofs.Lime1.sound allocated edge

theorem lime_step_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {b : Wasm.Lime1.Execution.Config H} (guard : Admitted fn a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller addr fn a) b ↔
      ∃ out, Edge fn a out ∧ b = limeConfig s caller addr fn out :=
  ⟨Proofs.Lime1.readback allocated guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound allocated edge⟩

theorem lime_run_iff (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc))
    {a : State} {b : Wasm.Lime1.Execution.Config H} (guard : Admitted fn a) :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step CallFrame.limeNoHost) (limeConfig s caller addr fn a) b ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ b = limeConfig s caller addr fn out :=
  Proofs.run_iff (limeConfig s caller addr fn) _ (fun e => lime_sound allocated e)
    (fun h step => (lime_step_iff allocated h).mp step) guard

end lime

section core
variable {H : Type} {P : Numerics.Profile} {s : Core.Store H}
  {caller : Frame} {addr : FuncAddr} {fn : CallFrame.Callee}

theorem core_sound (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a b : State} (edge : Edge fn a b) :
    Core.Step P noHost (coreConfig s caller addr fn a) (coreConfig s caller addr fn b) :=
  Proofs.core_sound allocated edge

theorem core_step_iff (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : State} {b : Core.Config H} (guard : Admitted fn a) :
    Core.Step P noHost (coreConfig s caller addr fn a) b ↔
      ∃ out, Edge fn a out ∧ b = coreConfig s caller addr fn out :=
  ⟨Proofs.core_readback allocated guard, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound allocated edge⟩

theorem core_run_iff (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : State} {b : Core.Config H} (guard : Admitted fn a) :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s caller addr fn a) b ↔
      ∃ out, Runs fn a out ∧ Admitted fn out ∧ b = coreConfig s caller addr fn out :=
  Proofs.run_iff (coreConfig s caller addr fn) _ (fun e => core_sound allocated e)
    (fun h step => (core_step_iff allocated h).mp step) guard

end core

open Wasm.Lime1.Execution in
theorem lime_invoke_strip_suffix {H : Type} {s : Store H} {f : Frame} {a : FuncAddr}
    {stack : List Value} {rest : List Admin} {dst : Config H}
    (step : Step CallFrame.limeNoHost ⟨s, f, values stack ++ .invoke a :: rest⟩ dst) :
    ∃ mid, Step CallFrame.limeNoHost ⟨s, f, values stack ++ [.invoke a]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, mid.code ++ rest⟩ :=
  Proofs.Lime1.invoke_strip_suffix step

open Wasm.Lime1.Execution in
theorem lime_intLoad_strip {H : Type} {s : Store H} {f : Frame} {arg : V1.MemArg}
    {ptr : BitVec 32} {saved : List Value} {tail : List Admin} {dst : Config H}
    (move : Step CallFrame.limeNoHost ⟨s, f, values (saved ++ [Value.int .i32 ptr]) ++ .source (.intLoad .i32 none arg) :: tail⟩ dst) :
    ∃ mid, Step CallFrame.limeNoHost ⟨s, f, [value (Value.int .i32 ptr), .source (.intLoad .i32 none arg)]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values saved ++ mid.code ++ tail⟩ :=
  Proofs.Lime1.intLoad_strip move

open Wasm.Lime1.Execution in
theorem lime_intStore_strip {H : Type} {s : Store H} {f : Frame} {arg : V1.MemArg}
    {ptr word : BitVec 32} {saved : List Value} {tail : List Admin} {dst : Config H}
    (move : Step CallFrame.limeNoHost ⟨s, f, values (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) ++
      .source (.intStore .i32 none arg) :: tail⟩ dst) :
    ∃ mid, Step CallFrame.limeNoHost ⟨s, f, [value (Value.int .i32 ptr), value (Value.int .i32 word),
      .source (.intStore .i32 none arg)]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values saved ++ mid.code ++ tail⟩ :=
  Proofs.Lime1.intStore_strip move

open Wasm.Lime1.Execution in
theorem lime_frame_context_inv {H : Type} {s : Store H} {f inside : Frame} {n : Nat}
    {saved : List Value} {code rest : List Admin} {dst : Config H}
    (step : Step CallFrame.limeNoHost ⟨s, f, values saved ++ .frame n inside code :: rest⟩ dst) :
    ∃ mid, Step CallFrame.limeNoHost ⟨s, f, [.frame n inside code]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values saved ++ mid.code ++ rest⟩ :=
  Proofs.Lime1.frame_context_inv step

open Wasm.Lime1.Execution in
theorem lime_label_context_cases {H : Type} {s : Store H} {f : Frame} {n : Nat} {cont : Wasm.Lime1.Expr}
    {saved : List Value} {code rest : List Admin} {dst : Config H}
    (step : Step CallFrame.limeNoHost ⟨s, f, values saved ++ .label n cont code :: rest⟩ dst) :
    (∃ mid, Step CallFrame.limeNoHost ⟨s, f, code⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values saved ++ .label n cont mid.code :: rest⟩) ∨
    ∃ out, PureStep f.module.types [.label n cont code] out ∧ dst = ⟨s, f, values saved ++ out ++ rest⟩ :=
  Proofs.Lime1.label_context_cases step

/-- A live Lime1 callee step leaves the caller's pending instructions unchanged. -/
theorem lime_active_strip {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} {a : CallFrame.State} {dst : Wasm.Lime1.Execution.Config H}
    {suffix : List Wasm.Lime1.Execution.Admin} (live : Active a)
    (step : Wasm.Lime1.Execution.Step CallFrame.limeNoHost ⟨s, caller, CallFrame.limeCode addr fn a ++ suffix⟩ dst) :
    ∃ mid, Wasm.Lime1.Execution.Step CallFrame.limeNoHost (CallFrame.limeConfig s caller addr fn a) mid ∧
      dst = ⟨mid.store, mid.frame, mid.code ++ suffix⟩ :=
  Proofs.Lime1.active_strip live step

/-- A live Core callee step leaves the caller's pending instructions unchanged. -/
theorem core_active_strip {H : Type} {P : Numerics.Profile} {s : Core.Store H} {caller : Frame}
    {addr : FuncAddr} {fn : CallFrame.Callee} (allocated : s.funcs[addr.value]? = some fn.coreInstance)
    {a : CallFrame.State} {dst : Core.Config H} {suffix : List Core.Admin} (live : Active a)
    (step : Core.Step P noHost ⟨s, caller.toCore, CallFrame.coreCode addr fn a ++ suffix⟩ dst) :
    ∃ mid, Core.Step P noHost (CallFrame.coreConfig s caller addr fn a) mid ∧
      dst = ⟨mid.store, mid.frame, mid.code ++ suffix⟩ :=
  Proofs.active_strip allocated live step

theorem config_toLime_injective (H : Type) :
    Function.Injective (Wasm.V1.Execution.Config.toLime (H := H)) :=
  Proofs.config_toLime_injective H

theorem listToCore_append {H : Type} (s : Wasm.Lime1.Execution.Store H)
    (a b : List Wasm.Lime1.Execution.Admin) :
    Wasm.Lime1.Execution.Admin.listToCore s (a ++ b) =
      Wasm.Lime1.Execution.Admin.listToCore s a ++ Wasm.Lime1.Execution.Admin.listToCore s b :=
  Proofs.core_append s a b

theorem values_toCore {H : Type} (s : Wasm.Lime1.Execution.Store H) (vs : List Value) :
    Wasm.Lime1.Execution.Admin.listToCore s (Wasm.Lime1.Execution.values vs) =
      Core.vals (vs.map Value.toCore) :=
  Proofs.core_values s vs

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame)
    (addr : FuncAddr) (fn : CallFrame.Callee) (q : State) :
    (v1Config s caller addr fn q).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) caller addr fn q :=
  Proofs.v1_to_lime s caller addr fn q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} (caller : Frame)
    {addr : FuncAddr} {fn : CallFrame.Callee}
    (allocated : s.funcs[addr.value]? = some (.wasm fn.type fn.module fn.limeFunc)) (q : State) :
    (limeConfig s caller addr fn q).toCore = coreConfig s.toCore caller addr fn q :=
  Proofs.lime_to_core caller allocated q

end Silmaril.Wasm.Institution.Operational.CallContinuation
