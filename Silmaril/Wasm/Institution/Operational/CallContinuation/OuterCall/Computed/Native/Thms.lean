module

public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Native.Defs
public import Silmaril.Wasm.Lime1.Execution.Callout
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed

open Execution
open Execution.Runtime (Frame FuncAddr Value)
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

theorem core_body_step_cases {H : Type} {P : Profile} {s : Core.Store H} {caller inner : Core.Frame}
    {n k : Nat} {cont : List Instr} {body : List Core.Admin} {dst : Core.Config H}
    (h : Core.Step P noHost ⟨s, caller, [.frame n inner [.label k cont body]]⟩ dst) :
    (∃ mid : Core.Config H, Core.Step P noHost ⟨s, inner, body⟩ mid ∧
      dst = ⟨mid.store, caller, [.frame n mid.frame [.label k cont mid.code]]⟩) ∨
    ∃ out, Core.LabelExit k cont body out ∧ dst = ⟨s, caller, [.frame n inner out]⟩ :=
  Proofs.Core.body_step_cases h

open Wasm.Lime1.Execution in
theorem lime_body_step_cases {H : Type} {s : Store H} {caller inner : Frame} {n k : Nat} {cont : Wasm.Lime1.Expr}
    {body : List Admin} {dst : Config H}
    (h : Step CallFrame.limeNoHost ⟨s, caller, [.frame n inner [.label k cont body]]⟩ dst) :
    (∃ mid : Config H, Step CallFrame.limeNoHost ⟨s, inner, body⟩ mid ∧
      dst = ⟨mid.store, caller, [.frame n mid.frame [.label k cont mid.code]]⟩) ∨
    ∃ out, PureStep inner.module.types [.label k cont body] out ∧ dst = ⟨s, caller, [.frame n inner out]⟩ :=
  Proofs.Lime1.body_step_cases h

theorem core_label_stays {n : Nat} {cont : List Instr} {stack : List Core.Val} {head : Core.Admin}
    {rest out : List Core.Admin} (none : head.val? = none) (notBr : ∀ i, head ≠ .plain (.br i))
    (notRet : head ≠ .plain .return_) (notTail : ¬ head.IsReturnCallRef)
    (notThrow : head ≠ .plain .throwRef) (notFinalTrap : head = .trap → stack ≠ [] ∨ rest ≠ [])
    (h : Core.LabelExit n cont (Core.vals stack ++ head :: rest) out) : False :=
  Proofs.Core.label_stays none notBr notRet notTail notThrow notFinalTrap h

open Wasm.Lime1.Execution in
theorem lime_label_stays {types : List Wasm.Lime1.FuncType} {n : Nat} {cont : Wasm.Lime1.Expr} {stack : List Value}
    {head : Admin} {rest out : List Admin} (none : asValue? head = none) (notBr : ∀ i, head ≠ .source (.br i))
    (notRet : head ≠ .source .return_) (notFinalTrap : head = .trap → stack ≠ [] ∨ rest ≠ [])
    (h : PureStep types [.label n cont (values stack ++ head :: rest)] out) : False :=
  Proofs.Lime1.label_stays none notBr notRet notFinalTrap h

theorem core_direct_call_iff {H : Type} {P : Profile} {s : Core.Store H} {f : Frame}
    {i : FuncIdx} {a : FuncAddr} {fn : Core.FuncInst H} {stack : List Value}
    {tail : List Core.Admin} {dst : Core.Config H}
    (lookup : f.module.funcs[i.toNat]? = some a) (alloc : s.funcs[a.value]? = some fn) :
    Core.Step P noHost ⟨s, f.toCore, coreValues stack ++ .plain (.call i) :: tail⟩ dst ↔
      dst = ⟨s, f.toCore, coreValues stack ++ .ref (.func a.value) :: .callRefType fn.type :: tail⟩ :=
  Proofs.Core.call_iff lookup alloc

theorem lime_direct_call_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {i : FuncIdx} {addr : FuncAddr} {stack : List Value} {tail : List Wasm.Lime1.Execution.Admin}
    {dst : Wasm.Lime1.Execution.Config H} (lookup : f.module.funcs[i.toNat]? = some addr) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost
      ⟨s, f, Wasm.Lime1.Execution.values stack ++ .source (.call i) :: tail⟩ dst ↔
      dst = ⟨s, f, Wasm.Lime1.Execution.values stack ++ .invoke addr :: tail⟩ :=
  Proofs.Lime1.call_iff lookup

open Wasm.Lime1.Execution in
theorem lime_call_indirect_iff {H : Type} {s : Store H} {f : Frame} {stack : List Value}
    {index : TypeIdx} {selector : BitVec 32} {table : Execution.Runtime.TableInst} {ft : V1.FuncType}
    {rest : List Admin} {dst : Config H}
    (tableFound : frameTable s f = some table) (typeFound : f.module.types[index.toNat]? = some ft) :
    Step CallFrame.limeNoHost
      ⟨s, f, values (stack ++ [Value.int .i32 selector]) ++ .source (.callIndirect index) :: rest⟩ dst ↔
      ((table.refs[selector.toNat]? = none ∨ table.refs[selector.toNat]? = some none) ∧
        dst = ⟨s, f, values stack ++ .trap :: rest⟩) ∨
      ∃ addr fn, table.refs[selector.toNat]? = some (some addr) ∧ s.funcs[addr.value]? = some fn ∧
        dst = ⟨s, f, values stack ++ (if fn.type = ft then .invoke addr else .trap) :: rest⟩ :=
  Proofs.Lime1.call_indirect_iff tableFound typeFound

open Wasm.Lime1.Execution in
theorem lime_block_step_iff {H : Type} {s : Store H} {f : Frame} {bt : Wasm.Lime1.BlockType}
    {stack : List Value} {body : Wasm.Lime1.Expr} {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.block bt body) :: rest⟩ dst ↔
      ∃ (saved args : List Value) (ft : Wasm.Lime1.FuncType),
        stack = saved ++ args ∧ blockType? f.module.types bt = some ft ∧
        args.length = ft.params.length ∧
        dst = ⟨s, f, values saved ++ .label ft.results.length [] (values args ++ expression body) :: rest⟩ :=
  Proofs.Lime1.block_step_iff

open Wasm.Lime1.Execution in
theorem lime_block_iff {H : Type} {s : Store H} {f : Frame} {result : Option NumType}
    {stack : List Value} {body : Wasm.Lime1.Expr} {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.block (Blocks.limeType result) body) :: rest⟩ dst ↔
      dst = ⟨s, f, values stack ++ .label result.toList.length [] (expression body) :: rest⟩ :=
  Proofs.Lime1.block_iff

open Wasm.Lime1.Execution in
theorem lime_loop_step_iff {H : Type} {s : Store H} {f : Frame} {bt : Wasm.Lime1.BlockType}
    {stack : List Value} {body : Wasm.Lime1.Expr} {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.loop bt body) :: rest⟩ dst ↔
      ∃ (saved args : List Value) (ft : Wasm.Lime1.FuncType),
        stack = saved ++ args ∧ blockType? f.module.types bt = some ft ∧
        args.length = ft.params.length ∧
        dst = ⟨s, f, values saved ++ .label ft.params.length [.loop bt body] (values args ++ expression body) :: rest⟩ :=
  Proofs.Lime1.loop_step_iff

open Wasm.Lime1.Execution in
theorem lime_loop_iff {H : Type} {s : Store H} {f : Frame} {result : Option NumType}
    {stack : List Value} {body : Wasm.Lime1.Expr} {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.loop (Blocks.limeType result) body) :: rest⟩ dst ↔
      dst = ⟨s, f, values stack ++ .label 0 [.loop (Blocks.limeType result) body] (expression body) :: rest⟩ :=
  Proofs.Lime1.loop_iff

/-- Conditional selection consumes the last i32 operand and preserves the
surrounding code. Entering the selected block is a separate native step. -/
theorem core_if_iff {H : Type} {P : Profile} {s : Core.Store H} {f : Core.Frame}
    {saved : List Core.Val} {condition : BitVec 32} {bt : BlockType} {thenBody elseBody : List Instr}
    {rest : List Core.Admin} {dst : Core.Config H} :
    Core.Step P noHost
      ⟨s, f, Core.vals (saved ++ [.num ⟨.int .i32, condition⟩]) ++ .plain (.if_ bt thenBody elseBody) :: rest⟩ dst ↔
      dst = ⟨s, f, Core.vals saved ++ .plain (.block bt (if condition = 0 then elseBody else thenBody)) :: rest⟩ :=
  Proofs.Core.if_iff

open Wasm.Lime1.Execution in
theorem lime_if_iff {H : Type} {s : Store H} {f : Frame}
    {saved : List Value} {condition : BitVec 32} {bt : Wasm.Lime1.BlockType} {thenBody elseBody : Wasm.Lime1.Expr}
    {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost
      ⟨s, f, values (saved ++ [Value.int .i32 condition]) ++ .source (.if_ bt thenBody elseBody) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ .source (.block bt (if condition = 0 then elseBody else thenBody)) :: rest⟩ :=
  Proofs.Lime1.if_iff

/-- A conditional branch consumes its i32 and leaves the surrounding
operands and suffix in place. A nonzero operand leaves a pending branch. -/
theorem core_br_if_iff {H : Type} {P : Profile} {s : Core.Store H} {f : Core.Frame}
    {saved : List Core.Val} {condition : BitVec 32} {depth : LabelIdx}
    {rest : List Core.Admin} {dst : Core.Config H} :
    Core.Step P noHost
      ⟨s, f, Core.vals (saved ++ [.num ⟨.int .i32, condition⟩]) ++ .plain (.brIf depth) :: rest⟩ dst ↔
      dst = ⟨s, f, Core.vals saved ++ (if condition = 0 then [] else [.plain (.br depth)]) ++ rest⟩ :=
  Proofs.Core.br_if_iff

open Wasm.Lime1.Execution in
theorem lime_br_if_iff {H : Type} {s : Store H} {f : Frame}
    {saved : List Value} {condition : BitVec 32} {depth : LabelIdx} {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost
      ⟨s, f, values (saved ++ [Value.int .i32 condition]) ++ .source (.brIf depth) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ (if condition = 0 then [] else [.source (.br depth)]) ++ rest⟩ :=
  Proofs.Lime1.br_if_iff

/-- The unsigned i32 selects a zero-based table slot, or the default depth
when no slot exists. Selection preserves the operands below the index and
the instruction suffix. -/
theorem core_br_table_iff {H : Type} {P : Profile} {s : Core.Store H} {f : Core.Frame}
    {saved : List Core.Val} {selector : BitVec 32} {depths : List LabelIdx} {fallback : LabelIdx}
    {rest : List Core.Admin} {dst : Core.Config H} :
    Core.Step P noHost
      ⟨s, f, Core.vals (saved ++ [.i32 selector]) ++ .plain (.brTable depths fallback) :: rest⟩ dst ↔
      dst = ⟨s, f, Core.vals saved ++ .plain (.br (depths[selector.toNat]?.getD fallback)) :: rest⟩ :=
  Proofs.Core.br_table_iff

open Wasm.Lime1.Execution in
theorem lime_br_table_iff {H : Type} {s : Store H} {f : Frame}
    {saved : List Value} {selector : BitVec 32} {depths : List LabelIdx} {fallback : LabelIdx}
    {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost
      ⟨s, f, values (saved ++ [Value.int .i32 selector]) ++ .source (.brTable depths fallback) :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ .source (.br (depths[selector.toNat]?.getD fallback)) :: rest⟩ :=
  Proofs.Lime1.br_table_iff

theorem core_unreachable_iff {H : Type} {P : Profile} {s : Core.Store H} {f : Core.Frame}
    {stack : List Core.Val} {rest : List Core.Admin} {dst : Core.Config H} :
    Core.Step P noHost ⟨s, f, Core.vals stack ++ .plain .unreachable :: rest⟩ dst ↔
      dst = ⟨s, f, Core.vals stack ++ .trap :: rest⟩ :=
  Proofs.Core.unreachable_iff

open Wasm.Lime1.Execution in
theorem lime_unreachable_iff {H : Type} {s : Store H} {f : Frame}
    {stack : List Value} {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source .unreachable :: rest⟩ dst ↔
      dst = ⟨s, f, values stack ++ .trap :: rest⟩ :=
  Proofs.Lime1.unreachable_iff

open Core in
theorem core_set_read {H : Type} {P : Profile} {s : Store H} {f : Execution.Runtime.Frame}
    {stack : List Value} {index : LocalIdx} {rest : List Admin} {dst : Config H}
    (move : Step P noHost ⟨s, f.toCore, coreValues stack ++ .plain (.localSet index) :: rest⟩ dst) :
    ∃ saved v next, stack = saved ++ [v] ∧ Locals.Edge ⟨f.locals, [.value v, .set index]⟩ ⟨next, []⟩ ∧
      dst = ⟨s, (⟨next, f.module⟩ : Execution.Runtime.Frame).toCore, coreValues saved ++ rest⟩ :=
  Proofs.Core.set_read move

open Core in
theorem core_tee_read {H : Type} {P : Profile} {s : Store H} {f : Execution.Runtime.Frame}
    {stack : List Value} {index : LocalIdx} {rest : List Admin} {dst : Config H}
    (move : Step P noHost ⟨s, f.toCore, coreValues stack ++ .plain (.localTee index) :: rest⟩ dst) :
    ∃ saved v, stack = saved ++ [v] ∧
      Locals.Edge ⟨f.locals, [.value v, .tee index]⟩ ⟨f.locals, [.value v, .value v, .set index]⟩ ∧
      dst = ⟨s, f.toCore, coreValues (saved ++ [v, v]) ++ .plain (.localSet index) :: rest⟩ :=
  Proofs.Core.tee_read move

open Wasm.Lime1.Execution in
theorem lime_set_read {H : Type} {s : Store H} {f : Frame} {stack : List Value} {index : LocalIdx}
    {rest : List Admin} {dst : Config H}
    (move : Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.localSet index) :: rest⟩ dst) :
    ∃ saved v next, stack = saved ++ [v] ∧ Locals.Edge ⟨f.locals, [.value v, .set index]⟩ ⟨next, []⟩ ∧
      dst = ⟨s, ⟨next, f.module⟩, values saved ++ rest⟩ :=
  Proofs.Lime1.set_read move

open Wasm.Lime1.Execution in
theorem lime_tee_read {H : Type} {s : Store H} {f : Frame} {stack : List Value} {index : LocalIdx}
    {rest : List Admin} {dst : Config H}
    (move : Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.localTee index) :: rest⟩ dst) :
    ∃ saved v, stack = saved ++ [v] ∧
      Locals.Edge ⟨f.locals, [.value v, .tee index]⟩ ⟨f.locals, [.value v, .value v, .set index]⟩ ∧
      dst = ⟨s, f, values (saved ++ [v, v]) ++ .source (.localSet index) :: rest⟩ :=
  Proofs.Lime1.tee_read move

open Wasm.Lime1.Execution in
theorem lime_local_get_iff {H : Type} {s : Store H} {f : Frame} {stack : List Value} {i : LocalIdx}
    {v : Value} {rest : List Admin} {dst : Config H} (found : f.locals[i.toNat]? = some v) :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .source (.localGet i) :: rest⟩ dst ↔
      dst = ⟨s, f, values stack ++ value v :: rest⟩ :=
  Proofs.Lime1.local_get_iff found

open Wasm.Lime1.Execution in
theorem lime_drop_iff {H : Type} {s : Store H} {f : Frame} {stack : List Value} {v : Value}
    {rest : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values (stack ++ [v]) ++ .source .drop :: rest⟩ dst ↔
      dst = ⟨s, f, values stack ++ rest⟩ :=
  Proofs.Lime1.drop_iff

open Wasm.Lime1.Execution in
/-- Trap propagation erases a suffix of the operands and a prefix of the code
after the trap. A native context can leave either side partially intact. -/
theorem lime_trap_front_iff {H : Type} {s : Store H} {f : Frame} {stack : List Value}
    {tail : List Admin} {dst : Config H} :
    Step CallFrame.limeNoHost ⟨s, f, values stack ++ .trap :: tail⟩ dst ↔
      ∃ kept removed cut rest, stack = kept ++ removed ∧ tail = cut ++ rest ∧
        (removed ≠ [] ∨ cut ≠ []) ∧ dst = ⟨s, f, values kept ++ .trap :: rest⟩ :=
  Proofs.Lime1.trap_front_iff

theorem guard_to_lime {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    (g : V1Guard s caller site) : LimeGuard (s.mapCode Wasm.V1.Func.toLime) caller site :=
  Proofs.guard_to_lime g

theorem guard_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    (g : LimeGuard s caller site) : CoreGuard s.toCore caller site :=
  Proofs.guard_to_core g

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (caller : Frame) (site : Site) (q : State site) :
    (v1Config s caller site q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) caller site q :=
  Proofs.v1_to_lime s caller site q

theorem lime_to_core {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    (g : LimeGuard s caller site) (q : State site) :
    (limeConfig s caller site q).toCore = coreConfig s.toCore caller site q :=
  Proofs.lime_to_core g q

theorem core_sound {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame} {site : Site}
    {a b : State site} (guard : CoreGuard s caller site) (edge : Edge site a b) :
    Core.Step P noHost (coreConfig s caller site a) (coreConfig s caller site b) :=
  Proofs.Core.sound guard edge

theorem core_step_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame} {site : Site}
    {a : State site} {b : Core.Config H} (guard : CoreGuard s caller site) (ready : Admitted site a) :
    Core.Step P noHost (coreConfig s caller site a) b ↔
      ∃ out, Edge site a out ∧ b = coreConfig s caller site out :=
  ⟨Proofs.Core.readback guard ready, fun ⟨_, move, eq⟩ => eq.symm ▸ core_sound guard move⟩

theorem lime_sound {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    {a b : State site} (g : LimeGuard s caller site) (edge : Edge site a b) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller site a) (limeConfig s caller site b) :=
  Proofs.Lime1.sound g edge

theorem lime_step_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    {a : State site} {b : Wasm.Lime1.Execution.Config H} (g : LimeGuard s caller site) (ready : Admitted site a) :
    Wasm.Lime1.Execution.Step CallFrame.limeNoHost (limeConfig s caller site a) b ↔
      ∃ out, Edge site a out ∧ b = limeConfig s caller site out :=
  ⟨Proofs.Lime1.readback g ready, fun ⟨_, move, eq⟩ => eq.symm ▸ lime_sound g move⟩

theorem v1_sound {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    {a b : State site} (g : V1Guard s caller site) (edge : Edge site a b) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller site a) (v1Config s caller site b) :=
  Proofs.V1.sound g edge

theorem v1_step_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    {a : State site} {b : Wasm.V1.Execution.Config H} (g : V1Guard s caller site) (ready : Admitted site a) :
    Wasm.V1.Execution.Step CallFrame.v1NoHost (v1Config s caller site a) b ↔
      ∃ out, Edge site a out ∧ b = v1Config s caller site out :=
  ⟨Proofs.V1.readback g ready, fun ⟨_, move, eq⟩ => eq.symm ▸ v1_sound g move⟩

theorem core_run_iff {H : Type} {P : Profile} {s : Core.Store H} {caller : Runtime.Frame} {site : Site}
    {a : State site} {b : Core.Config H} (guard : CoreGuard s caller site) (ready : Admitted site a) :
    Core.Steps P noHost (coreConfig s caller site a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = coreConfig s caller site out :=
  Proofs.run_iff (coreConfig s caller site) _ guard.typed (fun e => core_sound guard e)
    (fun h => core_step_iff guard h) ready

theorem lime_run_iff {H : Type} {s : Wasm.Lime1.Execution.Store H} {caller : Frame} {site : Site}
    {a : State site} {b : Wasm.Lime1.Execution.Config H}
    (guard : LimeGuard s caller site) (ready : Admitted site a) :
    Wasm.Lime1.Execution.Steps CallFrame.limeNoHost (limeConfig s caller site a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = limeConfig s caller site out :=
  Proofs.run_iff (limeConfig s caller site) _ guard.typed (fun e => lime_sound guard e)
    (fun h => lime_step_iff guard h) ready

theorem v1_run_iff {H : Type} {s : Wasm.V1.Execution.Store H} {caller : Frame} {site : Site}
    {a : State site} {b : Wasm.V1.Execution.Config H}
    (guard : V1Guard s caller site) (ready : Admitted site a) :
    Wasm.V1.Execution.Steps CallFrame.v1NoHost (v1Config s caller site a) b ↔
      ∃ out, Runs site a out ∧ Admitted site out ∧ b = v1Config s caller site out :=
  Proofs.run_iff (v1Config s caller site) _ guard.typed (fun e => v1_sound guard e)
    (fun h => v1_step_iff guard h) ready

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed
