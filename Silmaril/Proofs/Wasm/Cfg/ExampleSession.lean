module

public import Silmaril.Wasm.Cfg.ExampleSession.Defs
public import Silmaril.Wasm.Cfg.Session.Thms
public import Silmaril.Wasm.Interp.ExampleX.Thms
public import Silmaril.Wasm.Validation.Check.Validate
public import Silmaril.Proofs.Wasm.Cfg.Session

@[expose] public section

/-!
# The CFG session of a host-free instance: regression fixtures (proofs)

Validation, allocation and the executable checks by kernel evaluation, the store's typing from
`prepare?_sound` and `Instantiate.ok`. The two activations are machine runs: the body of export
`0` is one block ending in `unreachable` (`MStepC.trap`), the body of export `1` one block falling
through to `exit` with the stack `7` (`MStepC.fall`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleSession

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp
open Silmaril.Games.Abstract
open Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Session
  Silmaril.Wasm.Cfg.ExampleSession
open Silmaril.Wasm.Interp.ExampleX
open Silmaril.Wasm.Abstract.XRecursion (closedCallX)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

theorem sesMod_valid :
    ((Validation.validate? sesMod).map fun mt => mt.imports.isEmpty) = some true := by
  decide +kernel
theorem sesPrep_some : (prepare? evalConst? ({} : Store Nat) sesMod []).isSome = true := by
  decide +kernel
theorem sesPrep_shape : sesPrep.1.code.isEmpty = true ∧ sesPrep.2.isNone = true := by
  decide +kernel
theorem sesStore_chkEB : storeChkEB tExt sesStore.funcs = true := by decide +kernel
theorem sesStore_wasmB : (sesStore.funcs.all fun fi => match fi.code with
    | .wasm _ => (Validation.DefType.funcType? fi.type).isSome
    | .host _ => false) = true := by decide +kernel

theorem sesPrep_eq : prepare? evalConst? ({} : Store Nat) sesMod [] = some sesPrep := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp sesPrep_some
  simp [sesPrep, hp]

/-- **`sesMod` instantiates to `sesPrep.1`**, at every profile and host. -/
theorem ses_instantiate (P : Numerics.Profile) (host : HostSemantics Nat) :
    Instantiate P host ({} : Store Nat) sesMod [] sesPrep.1 := by
  obtain ⟨mt, hmt, hnil⟩ : ∃ mt, Validation.validate? sesMod = some mt ∧ mt.imports.isEmpty := by
    rcases h : Validation.validate? sesMod with _ | mt
    · have hm := sesMod_valid
      simp [h] at hm
    · have hm := sesMod_valid
      simp only [h, Option.map_some, Option.some.injEq] at hm
      exact ⟨mt, rfl, hm⟩
  have himp : mt.imports = [] := List.isEmpty_iff.mp hnil
  have hvalid : ∃ xtE xtI, Validation.ModuleOk sesMod ⟨xtI, xtE⟩ ∧
      List.Forall₂ (ExternAddrOk ({} : Store Nat)) [] xtI :=
    ⟨mt.exports, mt.imports, by simpa using Validation.validate?_sound hmt,
      by rw [himp]; exact .nil⟩
  have hst : sesPrep.2 = none := Option.isNone_iff_eq_none.mp sesPrep_shape.2
  have h : Instantiate P host ({} : Store Nat) sesMod [] (sesPrep.1.withStart sesPrep.2) :=
    (prepare?_sound (P := P) (host := host) (c := sesPrep.1) (st := sesPrep.2) evalConst?_evalSound
      sesPrep_eq hvalid).2
  have hw : sesPrep.1.withStart sesPrep.2 = sesPrep.1 := by rw [hst]; rfl
  rwa [hw] at h

/-- **The store of the instance is typed.** -/
theorem sesStore_ok : StoreOk sesStore := by
  have hc : ConfigOk sesPrep.1 [] :=
    Instantiate.ok SingleThreaded.divHost_ok Binaryen.storeOk_empty
      (ses_instantiate (SingleThreaded.profile fun _ _ _ _ => false) SingleThreaded.divHost)
  exact SingleThreaded.ConfigOk.storeOk hc

theorem sesStore_chkE : StoreChkE tExt sesStore.funcs := by
  intro a fi fn ps rs hfi hcode hty
  have hb : funcChkEB tExt sesStore.funcs fi = true :=
    List.all_eq_true.mp sesStore_chkEB fi (List.mem_of_getElem? hfi)
  simpa only [funcChkEB, hcode, hty] using hb

theorem sesStore_wasmT : WasmFuncsT sesStore := by
  intro a fi hfi
  have hb := List.all_eq_true.mp sesStore_wasmB fi (List.mem_of_getElem? hfi)
  cases hc : fi.code with
  | wasm fn =>
    rw [hc] at hb
    obtain ⟨⟨ps, rs⟩, hty⟩ := Option.isSome_iff_exists.mp hb
    exact ⟨fn, ps, rs, rfl, hty⟩
  | host h => rw [hc] at hb; cases hb

/-- **The instance is in the host-free fragment** at its store. -/
theorem ses_hfOk : HFOk sesInst sesStore where
  noImports := rfl
  wf :=
    { storeOk := sesStore_ok
      addrs_length := rfl
      export_type := by
        rintro ⟨_ | _ | n, hj⟩
        · exact ⟨_, rfl, Validation.Expand.iff.2 rfl⟩
        · exact ⟨_, rfl, Validation.Expand.iff.2 rfl⟩
        · simp at hj; omega
      host_type := by
        intro a fi h hfi hc
        obtain ⟨fn, -, -, hcode, -⟩ := sesStore_wasmT a fi hfi
        rw [hcode] at hc; cases hc }
  wasm := sesStore_wasmT
  chk := sesStore_chkE

/-! ## The two activations on the CFG machine -/

section Machine

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem val_i32 (k : BitVec 32) : (Admin.plain (.intConst .i32 k)).val? = some (.i32 k) := rfl

/-- **Export `0` traps**: its single block ends in `unreachable`. -/
theorem trap_run (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C [.unreachable]) (initial [.unreachable] s f)
      ⟨.trap, [], [], s, f⟩ :=
  .single (MStepC.trap (b := ⟨[], 0⟩) (sg := ⟨[], some .unreachable⟩) rfl rfl ⟨[], .nil⟩)

/-- **Export `1` answers `7`**: its single block falls through to `exit` with the stack `7`. -/
theorem val_run (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C [.intConst .i32 7])
      (initial [.intConst .i32 7] s f) ⟨.exit, [.i32 7], [], s, f⟩ :=
  .single (MStepC.fall (b := ⟨[], 0⟩) (sg := ⟨[.intConst .i32 7], none⟩) rfl rfl
    (by simpa [expression] using (RunC.val (val_i32 7) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 7)] s f (.normal [.i32 7]))))

end Machine

theorem f0_spec : ∃ (fi : FuncInst Nat), sesStore.funcs[0]? = some fi ∧
    fi.code = .wasm ⟨⟨0⟩, [], [.unreachable]⟩ ∧
    Validation.DefType.funcType? fi.type = some ([], []) :=
  ⟨_, rfl, rfl, rfl⟩

theorem f1_spec : ∃ (fi : FuncInst Nat) (rs : List Validation.CValType),
    sesStore.funcs[1]? = some fi ∧
    fi.code = .wasm ⟨⟨1⟩, [], [.intConst .i32 7]⟩ ∧
    Validation.DefType.funcType? fi.type = some ([], rs) ∧ rs.length = 1 :=
  ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- **A trap round**: export `0` traps on the CFG machine and keeps the store. -/
theorem trap_round (o : GrowOracle) :
    ([], .ret (.inr ()) sesStore) ∈ cfgFinS sesInst o sesStore trapQ := by
  obtain ⟨fi, hfi, hcode, hty⟩ := f0_spec
  refine ⟨rfl, .inl ⟨.trap, sesStore, .trap, rfl, by simp [Answer.ofResult?], fi, _, [], [],
    _, hfi, hcode, hty, trap_run _ _, rfl, rfl⟩⟩

/-- **A value round**: export `1` answers `7` on the CFG machine and keeps the store. -/
theorem val_round (o : GrowOracle) :
    ([], .ret (.inl ⟨valQ, .inl seven⟩) sesStore) ∈ cfgFinS sesInst o sesStore valQ := by
  obtain ⟨fi, rs, hfi, hcode, hty, hrs⟩ := f1_spec
  refine ⟨rfl, .inl ⟨.values seven, sesStore, .values [Val.i32 7], rfl, ?_, fi, _, [], rs,
    _, hfi, hcode, hty, val_run _ _, ?_, rfl⟩⟩
  · simp only [Answer.ofResult?]
    split
    · rfl
    · next h => exact absurd seven.2 h
  · simp [sinkResult, hrs]

/-- **The session repeats the trap forever**, resuming from the trap store each time. -/
theorem trap_forever (o : GrowOracle) :
    StratSession.sroundsPlay (fun _ => trapQ) (fun _ => ([], .inr ())) ∈
      (cfgSession sesInst o sesStore).inf :=
  (mem_inf_cfgSession ses_hfOk).2 ⟨_, _, _, infRounds_repeat (trap_round o), rfl⟩

/-- **The session alternates traps and answers forever.** -/
theorem alt_forever (o : GrowOracle) :
    StratSession.sroundsPlay altQ altR ∈ (cfgSession sesInst o sesStore).inf := by
  refine (mem_inf_cfgSession ses_hfOk).2 ⟨altQ, altR, fun _ => sesStore, ⟨rfl, fun k => ?_⟩, rfl⟩
  unfold altQ altR
  split
  · exact trap_round o
  · exact val_round o

end Silmaril.Wasm.Cfg.Proofs.ExampleSession
