module

public import Silmaril.Wasm.Cfg.DanglingExn.Defs
public import Silmaril.Wasm.Cfg.ExampleHostExn.Thms
public import Silmaril.Wasm.Game.SpecInst.Thms
public import Silmaril.Proofs.Wasm.Cfg.ExampleHostExnRun
public import Silmaril.Proofs.Wasm.Cfg.DanglingExn
public import Silmaril.Proofs.Wasm.Cfg.DanglingExnFwd

@[expose] public section

/-!
# Dangling exception addresses: fixtures on `hxMod` (proofs)

`callH` (`try_table (result i32) (catch 0 0) (call 0)`) with the host answering `throw t` for a
dangling `t`: the logged CFG machine dispatches the exception by `DispL.raise`, since no clause
of the handler frame catches it (`Catches … none`, `catches_iff`). The Core run is obtained by the
forward theorem (`fin_sub`). Aliasing: `hxStore` has no exception, so address `0` is dangling; a
Wasm `throw` of `$e` allocates exactly at address `0`, in Core (`Step.throw`) and natively
(`EvalLXPh.throw`), after which `catch 0 0` catches address `0`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingExn

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.CfgSession Silmaril.Wasm.Cfg.CfgClosure Silmaril.Wasm.Cfg.ExampleHostExn
  Silmaril.Wasm.Cfg.DanglingExn
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Cfg.Region (Catches)
open Silmaril.Wasm.Cfg.Proofs.ExampleRegress (mem_close)
open Silmaril.Wasm.Cfg.Proofs.ExampleHostExn (tryFr armAt fr0 call_enter f0_of host_beh)

/-! ## `callH` with a dangling host exception -/

section Machine

variable {H : Type} {s s' : Store H} {f : Frame} {fi0 : FuncInst H}

/-- **The host call of `callH` answered by a dangling exception**: `catch 0 0` does not catch it,
and the machine raises it. -/
theorem call_raise (hf0 : s.func? f ⟨0⟩ = some (0, fi0))
    (ht0 : DefType.funcType? fi0.type = some ([], [.i32])) {t : Nat} (hd : Dangling s' t) :
    MStepL callBody (armAt tryFr s f) [SCall.mk 0 [] s (.inl (.inr t)) s']
      ⟨.raise, [.ref (.exn t)], [], s', f⟩ := by
  have h := MStepL.run (body := callBody) (b := ⟨[(0, 0)], 0⟩) (ls := [tryFr]) (stk := []) rfl
    (fun _ h => nomatch h)
    (EvalLXPS.callThrow (es := []) (stk := []) (t := t) (s₂ := s') .nil hf0 ht0)
    (DispL.raise fun k L hL _ => by
      rcases k with _ | k
      · cases hL; exact (catches_iff hd).2 rfl
      · cases hL)
  simpa using h

end Machine

section Closure

variable {s s' : Store Nat} (hf : s.funcs = hxStore.funcs)
include hf

/-- **`callH` with the host throwing a dangling exception**: the exception is uncaught;
`callH` ends with it, in the host's store. -/
theorem callH_raise {t : Nat} (hd : Dangling s' t) :
    ([hostAns s (.throw t) s'], End.ret (.inl (.inr t)) s') ∈ Shape.close cfgHOpenXPS 1 s [] := by
  obtain ⟨fi0, -, hf0, -, ht0⟩ := f0_of hf
  obtain ⟨fi1, hfi1, hc1, hty1, hm1⟩ := Proofs.ExampleHostExn.hx_f1
  rw [← hf] at hfi1
  have hr : MRunL callBody (initial callBody s fr0) [SCall.mk 0 [] s (.inl (.inr t)) s']
      ⟨.raise, [.ref (.exn t)], [], s', fr0⟩ :=
    MRunL.step call_enter (MRunL.step (call_raise hf0 ht0 hd) (.refl _))
  refine mem_close (x := ([SCall.mk 0 [] s (.inl (.inr t)) s'], _)) (.inl ⟨fi1, _, [], [.i32],
    ⟨.raise, [.ref (.exn t)], [], s', fr0⟩, .throw t, .throw t, _, hfi1, hc1, hty1,
    by rw [hm1]; exact hr, trivial, ⟨t, rfl, rfl⟩, rfl, rfl⟩) ?_
  exact Shape.Subst.int (sh := Abstract.wasmHShapeS Nat) (c := Shape.close cfgHOpenXPS)
    (host_beh hf (.throw t) (.throw t) rfl s') (.nil _)

end Closure

theorem hx_dangling : Dangling hxStore 0 := Nat.le_refl 0

theorem callH_dangling_round :
    ([hostAns hxStore (.throw 0) hxStore], End.ret (.inl (.inr 0)) hxStore) ∈
      cfgEvFunDXPSC hxStore (1, []) :=
  .inl (callH_raise rfl hx_dangling)

theorem hx_invokeOk : InvokeOk hxStore 1 [] :=
  ⟨_, _, _, rfl, Expand.iff.2 rfl, .nil⟩

theorem hx_invOkXP : Abstract.InvOkXP hxStore.tags hxStore (1, []) :=
  ⟨hx_storeOk, hx_chk, Abstract.TypedCatValid.tagsOk_of_storeOk hx_storeOk, hx_invokeOk⟩

/-- **The same round in Core**, for every host in the slices that allows the answer. -/
theorem callH_dangling_core {P : Numerics.Profile} {host : HostSemantics Nat}
    (hH : Interp.HostSliceT host) (hE : Interp.HostSliceE hxStore.tags host)
    (hans : host 0 hxStore [] (.returned hxStore (.throw 0))) :
    Abstract.EvRun P host (invoke hxStore 1 []) [hostAns hxStore (.throw 0) hxStore]
      ⟨hxStore, {}, throwing 0⟩ := by
  have hx : ([hostAns hxStore (.throw 0) hxStore], End.ret (.inl (.inr 0)) hxStore) ∈
      (CfgInst.openRestrict (Abstract.coreHostRel host) Abstract.sessionTripleXP).1 hxStore
        (1, []) := by
    rw [← cfgSessionTripleC_eq]
    refine ⟨callH_dangling_round, ?_⟩
    rintro c (_ | ⟨_, ⟨⟩⟩)
    exact hans
  exact (fin_sub (P := P) hH hE hx_invOkXP hx).2

theorem hx_wf : hxI.WellFormed hxStore := by
  have h := hx_specInstance.ok.2
  rwa [hx_specInstance.store_eq] at h

theorem hx_instDom : CfgInst.InstDom hxI hxStore := ⟨hx_wf, hx_chk⟩

/-- The import call `h()` of `hxI`. -/
def hxE0 : hxI.E.Op := ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩

/-- **The unrestricted universal host of `hxI` answers `h()` by the dangling exception `0`.** -/
theorem hx_instHostU_throw : CfgInst.instHostU hxI 0 hxStore [] (.returned hxStore (.throw 0)) :=
  ⟨⟨hxE0, Proofs.CfgInst.importOp?_self hxE0, .throw 0, rfl⟩,
    Proofs.CfgInst.importsTyped_of_wf hx_wf 0, fun _ _ _ => trivial⟩

/-- **The round in Core at `instHostU hxI`**: `callH` ends with the dangling exception `0`. -/
theorem callH_dangling_core_U {P : Numerics.Profile} :
    Abstract.EvRun P (CfgInst.instHostU hxI) (invoke hxStore 1 [])
      [hostAns hxStore (.throw 0) hxStore] ⟨hxStore, {}, throwing 0⟩ :=
  callH_dangling_core hostSliceT_instHostU (hostSliceE_instHostU _) hx_instHostU_throw

/-! ## Aliasing -/

theorem hx_catches_before : Catches hxStore fr0 0 [catchE] none :=
  (catches_iff hx_dangling).2 rfl

theorem hx_catches_after (v : BitVec 32) :
    Catches (hxThrown v) fr0 0 [catchE] (some ([.i32 v], l0)) :=
  .catch_ (e := hxExn v) rfl rfl

theorem hx_core_alloc {P : Numerics.Profile} {host : HostSemantics Nat} (v : BitVec 32) :
    Step P host ⟨hxStore, fr0, [constI32 v, .plain (.throw ⟨0⟩)]⟩
      ⟨hxThrown v, fr0, throwing 0⟩ :=
  Step.throw (vs := [.i32 v]) (ts := .ofList [.i32]) rfl (Expand.iff.2 rfl) rfl

theorem hx_native_alloc (v : BitVec 32) :
    Abstract.EvalLXPh hxStore fr0 [.i32 v] [.op (.throw ⟨0⟩) []] []
      (hxThrown v, fr0, .flow (.throw 0)) :=
  Abstract.EvalLXPh.throw (ts := .ofList [.i32]) .nil rfl (Expand.iff.2 rfl) (Nat.le_refl 1)

end Silmaril.Wasm.Cfg.Proofs.DanglingExn
