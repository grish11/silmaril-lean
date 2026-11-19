module

public import Silmaril.Proofs.Wasm.Cfg.ExampleAlias
public import Silmaril.Wasm.Cfg.DanglingExn.Thms
public import Silmaril.Proofs.Wasm.Cfg.ExampleHostExnRun
public import Silmaril.Proofs.Wasm.Cfg.DanglingExnFwd

@[expose] public section

/-!
# A validated aliasing cycle through a dangling host exception: runs (proofs)

`run` on the logged CFG machine, from `alStore`, with the host answering `h()` by the dangling
exception `0`: `grab` enters its `try_table` and `catch_all_ref 0` catches the exception with its
own reference as the payload (`Catches.catchAllRef`), exiting with `ref.exn 0`; `run` then throws
`$t` with that payload, allocating `alCyc = ⟨0, [ref.exn 0]⟩` at address `0` (`EvalLXPS.throw`), and
raises it (`DispL.raise`, no handler). The Core run at `instHostU alI` is the forward theorem
(`DanglingExn.fin_sub`) applied to this round.
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleAlias

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.CfgSession Silmaril.Wasm.Cfg.CfgClosure Silmaril.Wasm.Cfg.ExampleAlias
open Silmaril.Wasm.Abstract (EvalLXPS SCall)
open Silmaril.Wasm.Cfg.Region (Catches)
open Silmaril.Wasm.Cfg.Proofs.ExampleRegress (mem_close)

/-! ## The store -/

theorem al_f0 : ∃ fi : FuncInst Nat, alStore.funcs[0]? = some fi ∧ fi.code = .host 0 ∧
    DefType.funcType? fi.type = some ([], []) := ⟨_, rfl, rfl, rfl⟩

theorem al_f1 : ∃ fi : FuncInst Nat, alStore.funcs[1]? = some fi ∧
    fi.code = .wasm ⟨⟨1⟩, [], runBody⟩ ∧ DefType.funcType? fi.type = some ([], []) ∧
    fi.module = alMI := ⟨_, rfl, rfl, rfl, rfl⟩

theorem al_f2 : ∃ (fi : FuncInst Nat) (rs : List CValType), alStore.funcs[2]? = some fi ∧
    fi.code = .wasm ⟨⟨2⟩, [], grabBody⟩ ∧ DefType.funcType? fi.type = some ([], rs) ∧
    rs.length = 1 ∧ fi.module = alMI := ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩

theorem alMI_funcs : alMI.funcs = [0, 1, 2] := rfl

theorem alStore_exns : alStore.exns = [] := rfl

/-- The label frame of `grab`'s `try_table (result exnref) (catch_all_ref 0)`. -/
abbrev grabFr : LFrame := ⟨1, [], false, true, [.catchAllRef l0], .value exnRef⟩

/-! ## The machine -/

theorem grab_enter :
    MStepL grabBody (initial grabBody alStore alFr) []
      ⟨.block ⟨[(0, 0)], 0⟩, [], [grabFr], alStore, alFr⟩ :=
  MStepL.enter (b := ⟨[], 0⟩) (a := 0) (V := []) (V' := []) rfl rfl rfl .tryTable .nil
    (.plain (fun _ _ _ => nofun)) rfl rfl

/-- **`catch_all_ref 0` catches the dangling host exception `0`**, with `ref.exn 0` as payload. -/
theorem grab_catch :
    MStepL grabBody ⟨.block ⟨[(0, 0)], 0⟩, [], [grabFr], alStore, alFr⟩
      [SCall.mk 0 [] alStore (.inl (.inr 0)) alStore]
      ⟨.exit, [.ref (.exn 0)], [], alStore, alFr⟩ := by
  obtain ⟨fi0, hfi0, -, ht0⟩ := al_f0
  have hf0 : alStore.func? alFr ⟨0⟩ = some (0, fi0) := by
    simp [Store.func?, Frame.forCall, alMI_funcs, hfi0, Idx.toNat]
  have h := MStepL.run (body := grabBody) (b := ⟨[(0, 0)], 0⟩) (ls := [grabFr]) (stk := []) rfl
    (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk)
    (EvalLXPS.callThrow (es := [.op .unreachable []]) (stk := []) (t := 0) (s₂ := alStore) .nil
      hf0 ht0)
    (DispL.catchOut (j := 0) (l := l0) (fun _ _ hk => absurd hk (Nat.not_lt_zero _)) rfl rfl
      Catches.catchAllRef rfl)
  simpa using h

/-- **`run` throws the reference it got**: `throw 0` allocates `alCyc` at address `0` and raises
it. -/
theorem run_raise :
    MStepL runBody (initial runBody alStore alFr)
      [SCall.mk 2 [] alStore (.inl (.inl [.ref (.exn 0)])) alStore]
      ⟨.raise, [.ref (.exn 0)], [], alEnd, alFr⟩ := by
  obtain ⟨fi2, rs, hfi2, -, ht2, -, -⟩ := al_f2
  have hf2 : alStore.func? alFr ⟨2⟩ = some (2, fi2) := by
    simp [Store.func?, Frame.forCall, alMI_funcs, hfi2, Idx.toNat]
  have hev : EvalLXPS alStore alFr [] (liftInstrs runBody)
      [SCall.mk 2 [] alStore (.inl (.inl [.ref (.exn 0)])) alStore]
      (alEnd, alFr, .flow (.throw 0)) := by
    have h := EvalLXPS.callRet (l₁ := []) (l₂ := []) (ws := [.ref (.exn 0)]) (s₂ := alStore)
      (stk := []) (es := [.op (.throw ⟨0⟩) []]) (args := []) .nil hf2 ht2
      (EvalLXPS.throw (stk₁ := [.ref (.exn 0)]) .nil rfl (Expand.iff.2 rfl) (by decide))
    exact h
  exact MStepL.run (b := ⟨[], 0⟩) rfl (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk) hev
    (DispL.raise fun _ _ h _ => by simp at h)

/-! ## The closure -/

theorem host_beh :
    ([alAns], End.ret (.inl (.inr 0)) alStore) ∈ Shape.close cfgHOpenXPS 0 alStore [] := by
  obtain ⟨fi, hfi, hc, hty⟩ := al_f0
  exact mem_close (x := (([⟨.inl (0, alStore, []), (alStore, .throw 0)⟩] : List (SCall Nat)), _))
    (.inr (.inr ⟨fi, 0, [], [], alStore, .throw 0, .throw 0, hfi, hc, hty, rfl, rfl⟩))
    (.ext (.nil _))

theorem grab_beh :
    ([alAns], End.ret (.inl (.inl [.ref (.exn 0)])) alStore) ∈
      Shape.close cfgHOpenXPS 2 alStore [] := by
  obtain ⟨fi2, rs, hfi2, hc2, hty2, hrs, hm2⟩ := al_f2
  refine mem_close (x := ([SCall.mk 0 [] alStore (.inl (.inr 0)) alStore], _)) (.inl ⟨fi2, _, [],
    rs, ⟨.exit, [.ref (.exn 0)], [], alStore, alFr⟩, .normal [.ref (.exn 0)],
    .normal [.ref (.exn 0)], _, hfi2, hc2, hty2,
    by rw [hm2]; exact MRunL.step grab_enter (MRunL.step grab_catch (.refl _)), trivial,
    ⟨_, rfl, rfl⟩, by simp [hrs, Abstract.exitFlow], rfl⟩) ?_
  exact Shape.Subst.int (sh := Abstract.wasmHShapeS Nat) (c := Shape.close cfgHOpenXPS)
    host_beh (.nil _)

/-- **`run` on the CFG closure**: the host's dangling exception `0` is caught by `grab`, and
`run` raises the self-referencing exception it allocates at address `0`. -/
theorem run_beh :
    ([alAns], End.ret (.inl (.inr 0)) alEnd) ∈ Shape.close cfgHOpenXPS 1 alStore [] := by
  obtain ⟨fi1, hfi1, hc1, hty1, hm1⟩ := al_f1
  refine mem_close (x := ([SCall.mk 2 [] alStore (.inl (.inl [.ref (.exn 0)])) alStore], _))
    (.inl ⟨fi1, _, [], [], ⟨.raise, [.ref (.exn 0)], [], alEnd, alFr⟩, .throw 0, .throw 0, _,
      hfi1, hc1, hty1, by rw [hm1]; exact MRunL.step run_raise (.refl _), trivial, ⟨0, rfl, rfl⟩,
      rfl, rfl⟩) ?_
  exact Shape.Subst.int (sh := Abstract.wasmHShapeS Nat) (c := Shape.close cfgHOpenXPS)
    grab_beh (.nil _)

/-- **The round on the CFG session triple.** -/
theorem run_round :
    ([alAns], End.ret (.inl (.inr 0)) alEnd) ∈ cfgSessionTripleC.1 alStore (1, []) :=
  .inl run_beh

/-! ## Core -/

theorem al_invokeOk : InvokeOk alStore 1 [] :=
  ⟨_, _, _, rfl, Expand.iff.2 rfl, .nil⟩

theorem al_invOkXP : Abstract.InvOkXP alStore.tags alStore (1, []) :=
  ⟨al_storeOk, al_chk, Abstract.TypedCatValid.tagsOk_of_storeOk al_storeOk, al_invokeOk⟩

/-- The import call `h()` of `alI`. -/
def alE0 : alI.E.Op := ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩

/-- **The unrestricted universal host of `alI` answers `h()` by the dangling exception `0`.** -/
theorem al_instHostU_throw :
    CfgInst.instHostU alI 0 alStore [] (.returned alStore (.throw 0)) :=
  ⟨⟨alE0, Proofs.CfgInst.importOp?_self alE0, .throw 0, rfl⟩,
    Proofs.CfgInst.importsTyped_of_wf al_wf 0, fun _ _ _ => trivial⟩

/-- **The same round in Core at `instHostU alI`**, every profile: the same host event, the
exception `0` uncaught, in the store `alEnd`. -/
theorem run_core_U {P : Numerics.Profile} :
    Abstract.EvRun P (CfgInst.instHostU alI) (invoke alStore 1 []) [alAns]
      ⟨alEnd, {}, throwing 0⟩ := by
  have hx : ([alAns], End.ret (.inl (.inr 0)) alEnd) ∈
      (CfgInst.openRestrict (Abstract.coreHostRel (CfgInst.instHostU alI))
        Abstract.sessionTripleXP).1 alStore (1, []) := by
    rw [← cfgSessionTripleC_eq]
    refine ⟨run_round, ?_⟩
    rintro c (_ | ⟨_, ⟨⟩⟩)
    exact al_instHostU_throw
  exact (DanglingExn.fin_sub (P := P) Proofs.DanglingExn.hostSliceT_instHostU
    (Proofs.DanglingExn.hostSliceE_instHostU _) al_invOkXP hx).2

/-- **The end store satisfies the relaxed store invariant**, carried along the Core run. -/
theorem alEnd_storeOkD : DanglingTyped.StoreOkD alEnd :=
  DanglingTyped.storeOkD_of_configOkD (c := ⟨alEnd, {}, throwing 0⟩)
    (DanglingTyped.ConfigOkD.evRun (P := SingleThreaded.profile SingleThreaded.neverFail)
      DanglingTyped.hostTypedD_instHostU
      (DanglingTyped.configOkD_invoke_of_storeOk al_storeOk al_funcsSupp al_invokeOk) run_core_U)

end Silmaril.Wasm.Cfg.Proofs.ExampleAlias
