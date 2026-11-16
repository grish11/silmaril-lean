module

public import Silmaril.Wasm.Component.Param.StartCore3.Defs
public import Silmaril.Proofs.Wasm.Component.Param.Start
public import Silmaril.Proofs.Wasm.Component.Param.SpecToIR
public import Silmaril.Proofs.Wasm.Component.Reference.Litmus
public import Silmaril.Proofs.Wasm.Component.Core3G.Sim
public import Silmaril.Proofs.Wasm.Component.Core3G.Lawful
public import Silmaril.Wasm.Component.Reference.Thms
public import Silmaril.Wasm.Component.Binary.Lower.Sem.Thms

/-!
# Start functions on the Core 3.0 engine: proofs

The instances are computed by kernel evaluation of `prepareE?` (`decide +kernel` on a Boolean
summary), for the binaries after `Binary.Core.decode?`. The runs of the start functions and of `get` are Core 3.0 runs built from `Step` rules,
for every profile: `global.set` then `global.get` for `startMod`, `unreachable` for
`trapStartMod`. That a trapping start function can reach nothing else uses determinism of the
deterministic profiles `profile o` (`Silmaril.Wasm.Game.reach_normal_unique`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Param.StartCore3

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.Param.StartCore3
open Silmaril.Wasm.Component.Reference.Litmus (startMod startCore3)
open Silmaril.Wasm.Validation (Expand)
open Silmaril.Wasm.Component.Engine.Core3 (prepareE? instExports)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Game (FnType Reach ResultAt statusP)
open Silmaril.Wasm.Numerics (Profile)

/-- Runs of an engine. -/
local notation "ESteps" => Silmaril.Wasm.Component.Engine.CoreEngine.Steps

/-- Core values. -/
local notation "CVal" => Silmaril.Wasm.Execution.Core.Val

/-- The Core value `i32 42`. -/
local notation "v42" => Silmaril.Wasm.Execution.Core.Val.i32 42

/-- Core steps. -/
local notation "CStep" => Silmaril.Wasm.Execution.Core.Step

/-! ## Instances -/

/-- An instance of `core3P P` with exports at `[1]` and start function at `0`. -/
def startSI (P : Profile) (s : Store Nat) : SInstance (core3P P) where
  store := s
  addrs := [(1 : Nat)]
  start := some (0 : Nat)

/-- The function type `[] → []`. -/
abbrev unitFn : FnType := ⟨[], []⟩

/-- The function type `[] → [i32]`. -/
abbrev getFn : FnType := ⟨[], [.num (.int .i32)]⟩

/-- The function instance has no locals and the body `i32.const 42; global.set 0`. -/
def isSet (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.intConst .i32 v, .globalSet x]⟩ => v == 42 && x.toNat == 0
  | _ => false

/-- The function instance has no locals and the body `global.get 0`. -/
def isGet (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.globalGet x]⟩ => x.toNat == 0
  | _ => false

/-- The function instance has no locals and the body `unreachable`. -/
def isUnreachable (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.unreachable]⟩ => true
  | _ => false

/-- The checks on preparing a module: the start function is at address `0`, has type
`[] → []` and passes `S`; `get` is exported at address `1`. -/
def prepOk (S : FuncInst Nat → Bool) : Option (Store Nat × ModuleInst × Option Nat) → Bool
  | some (s, inst, some 0) =>
    (instExports inst).lookup "get" == some (.func 1) &&
      match s.funcs[0]? with
      | some f0 => FnType.ofDefType? f0.type == some unitFn && S f0
      | none => false
  | _ => false

/-- The checks of `startCore3`: both functions share a module instance whose global `0` is at
an address `a` of the store, and `get` has type `[] → [i32]`. -/
def startOk : Option (Store Nat × ModuleInst × Option Nat) → Bool
  | some (s, _, _) =>
    match s.funcs[0]?, s.funcs[1]? with
    | some f0, some f1 =>
      FnType.ofDefType? f1.type == some getFn && isGet f1 &&
        match f0.module.globals[0]? with
        | some a => f1.module.globals[0]? == some a && (s.globals[a]?).isSome
        | none => false
    | _, _ => false
  | none => false

/-- The prepared instance of `startCore3`. -/
def startPrep : Option (Store Nat × ModuleInst × Option Nat) := prepareE? {} startCore3 []

/-- The prepared instance of `trapStartCore3`. -/
def trapPrep : Option (Store Nat × ModuleInst × Option Nat) := prepareE? {} trapStartCore3 []

theorem startPrep_prepOk : prepOk isSet startPrep = true := by decide +kernel

theorem startPrep_startOk : startOk startPrep = true := by decide +kernel

theorem trapPrep_ok : prepOk isUnreachable trapPrep = true := by decide +kernel

/-- The store of a prepared instance. -/
def storeOf : Option (Store Nat × ModuleInst × Option Nat) → Store Nat
  | some (s, _, _) => s
  | none => {}

/-- What `prepOk` records. -/
theorem prepOk_eq {S : FuncInst Nat → Bool} {o : Option (Store Nat × ModuleInst × Option Nat)}
    (h : prepOk S o = true) :
    ∃ inst f0, o = some (storeOf o, inst, some 0) ∧
      (instExports inst).lookup "get" = some (.func 1) ∧ (storeOf o).funcs[0]? = some f0 ∧
      FnType.ofDefType? f0.type = some unitFn ∧ S f0 = true := by
  match o, h with
  | some (s, inst, some 0), h =>
    simp only [prepOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hl, h⟩ := h
    split at h
    next f0 hf0 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨inst, f0, rfl, hl, hf0, h.1, h.2⟩
    next => cases h

/-- The engine instance of a module whose preparation passes `prepOk`. -/
theorem instOfS_of_prepOk (P : Profile) {S : FuncInst Nat → Bool} {m : Silmaril.Wasm.Module}
    (h : prepOk S (prepareE? {} m []) = true) (ft : CoreFuncTy) :
    instOfS (core3P P) m [] [("get", ft)] = some (startSI P (storeOf (prepareE? {} m []))) := by
  obtain ⟨inst, f0, hp, hl, -⟩ := prepOk_eq h
  have hp' : (core3P P).prepare? (H := Nat) ((core3P P).empty Nat) m [] =
      some (storeOf (prepareE? {} m []), inst, some (0 : Nat)) := hp
  have he : exportAddrs (core3P P) inst [("get", ft)] = some [(1 : Nat)] := by
    unfold exportAddrs
    show List.mapM (fun x => ((instExports inst).lookup x.1).bind
      Silmaril.Wasm.Component.Engine.Core3.asFunc?) [("get", ft)] = some [1]
    simp [hl, Silmaril.Wasm.Component.Engine.Core3.asFunc?]
  unfold instOfS
  simp only [allocHosts, List.map_nil, hp', he]
  rfl

/-! ## Runs -/

open Silmaril.Proofs.Wasm.Component.Reference.Litmus (steps_frame_label reach_of_steps)

/-- `i32.const 42; global.set x` sets the global. -/
theorem set_run {P : Profile} {s : Store Nat} {f0 : FuncInst Nat} {code : Silmaril.Wasm.Func}
    {x : Silmaril.Wasm.GlobalIdx} {a : Nat} {g : GlobalInst}
    (hf : s.funcs[0]? = some f0) (hty : FnType.ofDefType? f0.type = some unitFn)
    (hcode : f0.code = .wasm code) (hloc : code.locals = [])
    (hbody : code.body = [.intConst .i32 42, .globalSet x])
    (hg : s.global? (Frame.forCall f0.module [] []) x = some (a, g)) :
    Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s 0 [])
      ⟨s.setGlobal a (v42), {}, vals []⟩ := by
  have he : Expand f0.type unitFn.toComp := FnType.expand_of_ofDefType? hty
  let F := Frame.forCall f0.module [] code.locals
  have hF : F = Frame.forCall f0.module [] [] := by simp [F, hloc]
  have s₁ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s 0 [])
      ⟨s, {}, [.frame 0 F [.label 0 [] (expression code.body)]]⟩ :=
    .callRefFunc (vs := []) (c := .callRefType ((s.funcs[0]?.map FuncInst.type).getD default))
      trivial hf he rfl hcode
  have s₂ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, F, expression code.body⟩ ⟨s.setGlobal a (v42), F, vals []⟩ := by
    rw [hbody]
    exact .variable (.globalSet (v := v42) (hF ▸ hg))
  have s₃ := steps_frame_label (f := {}) (n := 0) (m := 0) (cont := [])
    (Relation.ReflTransGen.single s₂)
  have s₄ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s.setGlobal a (v42), {}, [.frame 0 F [.label 0 [] (vals [])]]⟩
      ⟨s.setGlobal a (v42), {}, [.frame 0 F (vals [])]⟩ :=
    .ctxtFrame .labelVals
  have s₅ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s.setGlobal a (v42), {}, [.frame 0 F (vals [])]⟩
      ⟨s.setGlobal a (v42), {}, vals []⟩ :=
    .frameVals rfl
  exact (Relation.ReflTransGen.single s₁).trans (s₃.tail s₄ |>.tail s₅)

/-- `global.get x` reads the global. -/
theorem get_run {P : Profile} {s : Store Nat} {f1 : FuncInst Nat} {code : Silmaril.Wasm.Func}
    {x : Silmaril.Wasm.GlobalIdx} {a : Nat} {g : GlobalInst}
    (hf : s.funcs[1]? = some f1) (hty : FnType.ofDefType? f1.type = some getFn)
    (hcode : f1.code = .wasm code) (hloc : code.locals = [])
    (hbody : code.body = [.globalGet x])
    (hg : s.global? (Frame.forCall f1.module [] []) x = some (a, g)) :
    Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s 1 []) ⟨s, {}, vals [g.value]⟩ := by
  have he : Expand f1.type getFn.toComp := FnType.expand_of_ofDefType? hty
  let F := Frame.forCall f1.module [] code.locals
  have hF : F = Frame.forCall f1.module [] [] := by simp [F, hloc]
  have s₁ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s 1 [])
      ⟨s, {}, [.frame 1 F [.label 1 [] (expression code.body)]]⟩ :=
    .callRefFunc (vs := []) (c := .callRefType ((s.funcs[1]?.map FuncInst.type).getD default))
      trivial hf he rfl hcode
  have s₂ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, F, expression code.body⟩ ⟨s, F, vals [g.value]⟩ := by
    rw [hbody]
    exact .variable (.globalGet (hF ▸ hg))
  have s₃ := steps_frame_label (f := {}) (n := 1) (m := 1) (cont := [])
    (Relation.ReflTransGen.single s₂)
  have s₄ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, {}, [.frame 1 F [.label 1 [] (vals [g.value])]]⟩ ⟨s, {}, [.frame 1 F (vals [g.value])]⟩ :=
    .ctxtFrame .labelVals
  have s₅ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, {}, [.frame 1 F (vals [g.value])]⟩ ⟨s, {}, vals [g.value]⟩ :=
    .frameVals rfl
  exact (Relation.ReflTransGen.single s₁).trans (s₃.tail s₄ |>.tail s₅)

/-- `unreachable` traps. -/
theorem trap_run {P : Profile} {s : Store Nat} {f0 : FuncInst Nat} {code : Silmaril.Wasm.Func}
    (hf : s.funcs[0]? = some f0) (hty : FnType.ofDefType? f0.type = some unitFn)
    (hcode : f0.code = .wasm code) (hbody : code.body = [.unreachable]) :
    Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s 0 []) ⟨s, {}, [.trap]⟩ := by
  have he : Expand f0.type unitFn.toComp := FnType.expand_of_ofDefType? hty
  let F := Frame.forCall f0.module [] code.locals
  have s₁ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s 0 [])
      ⟨s, {}, [.frame 0 F [.label 0 [] (expression code.body)]]⟩ :=
    .callRefFunc (vs := []) (c := .callRefType ((s.funcs[0]?.map FuncInst.type).getD default))
      trivial hf he rfl hcode
  have s₂ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, F, expression code.body⟩ ⟨s, F, [.trap]⟩ := by
    rw [hbody]
    exact .parametric .unreachable
  have s₃ := steps_frame_label (f := {}) (n := 0) (m := 0) (cont := [])
    (Relation.ReflTransGen.single s₂)
  have s₄ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, {}, [.frame 0 F [.label 0 [] [.trap]]]⟩ ⟨s, {}, [.frame 0 F [.trap]]⟩ :=
    .ctxtFrame .trapLabel
  have s₅ : CStep P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, {}, [.frame 0 F [.trap]]⟩ ⟨s, {}, [.trap]⟩ :=
    .trapFrame
  exact (Relation.ReflTransGen.single s₁).trans (s₃.tail s₄ |>.tail s₅)

/-- A host-free Core run from a thread is a run of `core3P P`. -/
theorem engineSteps_of_steps {P : Profile} {s : Store Nat}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {d : Config Nat}
    (h : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (t.config s) d) :
    ∃ s' t', ESteps (core3P P) (s, t) (s', t') ∧ t'.config s' = d := by
  obtain ⟨s', t', hr, hd⟩ := reach_of_steps h
  exact ⟨s', t', hr, hd⟩

/-- A run of `core3P P` from the invocation of `a` to the values `vs`, at a store reached from
`s` by a Core run. -/
theorem engineRun_values {P : Profile} {s s₁ : Store Nat} {a : Nat} {vs : List CVal}
    (h : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s a []) ⟨s₁, {}, vals vs⟩) :
    ∃ t', ESteps (core3P P) (s, (core3P P).invoke a []) (s₁, t') ∧
      (core3P P).status s₁ t' = flatStatus (.returned (.values vs)) := by
  obtain ⟨s', t', hr, hd⟩ := engineSteps_of_steps (t := .pending a []) h
  have hs : s' = s₁ :=
    (Silmaril.Wasm.SingleThreaded.Thread.config_store (H := Nat) s' t').symm.trans
      (congrArg Config.store hd)
  subst hs
  refine ⟨t', hr, ?_⟩
  show flatStatus (statusP P s' t') = _
  rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_values (congrArg Config.code hd)]

/-- A run of `core3P P` from the invocation of `a` to a trap. -/
theorem engineRun_trap {P : Profile} {s s₁ : Store Nat} {a : Nat}
    (h : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s a []) ⟨s₁, {}, [.trap]⟩) :
    ∃ t', ESteps (core3P P) (s, (core3P P).invoke a []) (s₁, t') ∧
      statusP P s₁ t' = .returned .trap := by
  obtain ⟨s', t', hr, hd⟩ := engineSteps_of_steps (t := .pending a []) h
  have hs : s' = s₁ :=
    (Silmaril.Wasm.SingleThreaded.Thread.config_store (H := Nat) s' t').symm.trans
      (congrArg Config.store hd)
  subst hs
  exact ⟨t', hr, Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_trap (congrArg Config.code hd)⟩

/-! ## `startMod` -/

/-- The store of `startCore3` before its start function. -/
abbrev startStore : Store Nat := storeOf startPrep

/-- What `prepOk isSet` and `startOk` record. -/
theorem start_facts {o : Option (Store Nat × ModuleInst × Option Nat)} (h1 : prepOk isSet o = true)
    (h2 : startOk o = true) : ∃ (inst : ModuleInst) (f0 f1 : FuncInst Nat) (c0 c1 : Silmaril.Wasm.Func)
    (x₀ x₁ : Silmaril.Wasm.GlobalIdx) (a : Nat) (g : GlobalInst),
    o = some (storeOf o, inst, some 0) ∧
    (instExports inst).lookup "get" = some (.func 1) ∧
    (storeOf o).funcs[0]? = some f0 ∧ FnType.ofDefType? f0.type = some unitFn ∧
    f0.code = .wasm c0 ∧ c0.locals = [] ∧ c0.body = [.intConst .i32 42, .globalSet x₀] ∧
    (storeOf o).funcs[1]? = some f1 ∧ FnType.ofDefType? f1.type = some getFn ∧
    f1.code = .wasm c1 ∧ c1.locals = [] ∧ c1.body = [.globalGet x₁] ∧
    f0.module.globals[x₀.toNat]? = some a ∧ f1.module.globals[x₁.toNat]? = some a ∧
    (storeOf o).globals[a]? = some g := by
  obtain ⟨inst, f0, hp, hl, hf0, hty0, hs0⟩ := prepOk_eq h1
  rw [hp] at h2
  simp only [startOk] at h2
  rw [hf0] at h2
  split at h2
  next f0' f1 hf0' hf1 =>
    cases (Option.some.inj hf0').symm
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨⟨hty1, hg1⟩, h2⟩ := h2
    unfold isSet at hs0
    split at hs0
    next c0 v x₀ hc0 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hs0
      obtain ⟨rfl, hx₀⟩ := hs0
      unfold isGet at hg1
      split at hg1
      next c1 x₁ hc1 =>
        have hx₁ : x₁.toNat = 0 := by simpa using hg1
        split at h2
        next a ha =>
          simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h2
          obtain ⟨ha1, g, hg⟩ := h2
          exact ⟨inst, f0, f1, _, _, x₀, x₁, a, g, hp, hl, hf0, hty0, hc0, rfl, rfl,
            hf1, hty1, hc1, rfl, rfl, hx₀ ▸ ha, hx₁ ▸ ha1, hg⟩
        next => cases h2
      next => cases hg1
    next => cases hs0
  next => cases h2

/-- `startMod`'s instance before its start function. -/
theorem startMod_instOfS (P : Profile) :
    instOfS (core3P P) startMod.mod (CoreModule.imports startMod) (CoreModule.exports startMod) =
      some (startSI P startStore) :=
  instOfS_of_prepOk P startPrep_prepOk _

/-- **`get()` returns `42` after the start function**, for a module whose preparation passes
`prepOk isSet` and `startOk`. -/
theorem get_of {m : Silmaril.Wasm.Module} (h1 : prepOk isSet (prepareE? {} m []) = true)
    (h2 : startOk (prepareE? {} m []) = true) (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ (some (.flat [Flat.i32 42])))] ∈
      engineStrategyS (core3P P) (startSI P (storeOf (prepareE? {} m []))) []
        [("get", ⟨[], [.int .i32]⟩)] := by
  obtain ⟨inst, f0, f1, c0, c1, x₀, x₁, a, g, -, -, hf0, hty0, hc0, hl0, hb0, hf1, hty1, hc1,
    hl1, hb1, ha0, ha1, hg⟩ := start_facts h1 h2
  have hg0 : (storeOf (prepareE? {} m [])).global? (Frame.forCall f0.module [] []) x₀ = some (a, g) := by
    simp [Store.global?, Frame.forCall, ha0, hg]
  obtain ⟨t₁, run₁, st₁⟩ := engineRun_values (P := P) (set_run hf0 hty0 hc0 hl0 hb0 hg0)
  let S₁ := (storeOf (prepareE? {} m [])).setGlobal a (v42)
  have hf1' : S₁.funcs[1]? = some f1 := hf1
  have hg1 : S₁.global? (Frame.forCall f1.module [] []) x₁ =
      some (a, { g with value := v42 }) := by
    simp [S₁, Store.global?, Store.setGlobal, Frame.forCall, ha1, List.getElem?_modify, hg]
  obtain ⟨t₂, run₂, st₂⟩ := engineRun_values (P := P) (get_run hf1' hty1 hc1 hl1 hb1 hg1)
  have hq : callee? (E := core3P P) [(1 : Nat)] [("get", ⟨[], [.int .i32]⟩)] getQ = some ((1 : Nat), []) := rfl
  have h2 := Silmaril.Proofs.Wasm.Component.Param.engineStrategy_two (imps := [])
    (I := ⟨S₁, [(1 : Nat)]⟩) hq run₂ (R := some (.flat [Flat.i32 42])) (.inl ⟨_, st₂, rfl⟩)
  have := Silmaril.Proofs.Wasm.Component.Param.engineStrategyS_start_mem (I := startSI P (storeOf (prepareE? {} m [])))
    rfl (.nil run₁) st₁ h2
  simpa using this

/-- **`startMod`'s `get()` returns `42` after the start function.** -/
theorem startMod_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ (some (.flat [Flat.i32 42])))] ∈
      engineStrategyS (core3P P) (startSI P startStore) [] startMod.exports :=
  get_of startPrep_prepOk startPrep_startOk P

/-- Over the old semantics, `startMod` traps on every question. -/
theorem startMod_engineSem (P : Profile) :
    (engineSem (core3P P) NumModule NumModule.mod).sem startMod = trapAll _ _ := by
  have h : instOf (core3P P) startMod.mod (CoreModule.imports startMod)
      (CoreModule.exports startMod) = none := by
    exact (Silmaril.Proofs.Wasm.Component.Param.instOf_eq _ _ _ _).trans
      (by simp only [startMod_instOfS]; rfl)
  simp only [engineSem, h]

theorem startMod_engineSemS (P : Profile) :
    (engineSemS (core3P P) NumModule NumModule.mod).sem startMod =
      engineStrategyS (core3P P) (startSI P startStore) [] startMod.exports := by
  simp only [engineSemS, startMod_instOfS]
  rfl

/-! ## `trapStartMod` -/

/-- The store of `trapStartCore3` before its start function. -/
abbrev trapStore : Store Nat := storeOf trapPrep

theorem trap_facts {pr : Option (Store Nat × ModuleInst × Option Nat)}
    (h : prepOk isUnreachable pr = true) : ∃ (inst : ModuleInst) (f0 : FuncInst Nat) (c0 : Silmaril.Wasm.Func), pr = some (storeOf pr, inst, some 0) ∧
    (instExports inst).lookup "get" = some (.func 1) ∧
    (storeOf pr).funcs[0]? = some f0 ∧ FnType.ofDefType? f0.type = some unitFn ∧
    f0.code = .wasm c0 ∧ c0.body = [.unreachable] := by
  obtain ⟨inst, f0, hp, hl, hf0, hty0, hs0⟩ := prepOk_eq h
  unfold isUnreachable at hs0
  split at hs0
  next c0 hc0 => exact ⟨inst, f0, _, hp, hl, hf0, hty0, hc0, rfl⟩
  next => cases hs0

theorem trapStartMod_instOfS (P : Profile) :
    instOfS (core3P P) trapStartMod.mod (CoreModule.imports trapStartMod)
      (CoreModule.exports trapStartMod) = some (startSI P trapStore) :=
  instOfS_of_prepOk P trapPrep_ok _

theorem trapStartMod_engineSemS (P : Profile) :
    (engineSemS (core3P P) NumModule NumModule.mod).sem trapStartMod =
      engineStrategyS (core3P P) (startSI P trapStore) [] trapStartMod.exports := by
  simp only [engineSemS, trapStartMod_instOfS]
  rfl

/-- The start run traps, for every profile. -/
theorem trap_engineRun {pr : Option (Store Nat × ModuleInst × Option Nat)}
    (h : prepOk isUnreachable pr = true) (P : Profile) :
    ∃ t', ESteps (core3P P) ((storeOf pr), (core3P P).invoke (0 : Nat) []) ((storeOf pr), t') ∧
      statusP P (storeOf pr) t' = .returned .trap := by
  obtain ⟨inst, f0, c0, -, -, hf0, hty0, hc0, hb0⟩ := trap_facts h
  exact engineRun_trap (trap_run hf0 hty0 hc0 hb0)

/-- **The first question is answered by a trap**, for every profile. -/
theorem trap_get {pr : Option (Store Nat × ModuleInst × Option Nat)}
    (h : prepOk isUnreachable pr = true) (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ none)] ∈
      engineStrategyS (core3P P) (startSI P (storeOf pr)) [] [("get", ⟨[], [.int .i32]⟩)] := by
  obtain ⟨t', run, ht⟩ := trap_engineRun h P
  have := Silmaril.Proofs.Wasm.Component.Param.engineStrategyS_start_trap
    (I := startSI P (storeOf pr)) (imps := []) (exps := [("get", ⟨[], [.int .i32]⟩)]) rfl (.nil run)
    (show flatStatus (statusP P (storeOf pr) t') = _ by rw [ht]; rfl) getQ
  simpa using this

/-- **In a deterministic profile, the instance traps on every question.** -/
theorem trap_eq_trapAll {pr : Option (Store Nat × ModuleInst × Option Nat)}
    (h : prepOk isUnreachable pr = true) (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    engineStrategyS (core3P (Silmaril.Wasm.SingleThreaded.profile o))
      (startSI (Silmaril.Wasm.SingleThreaded.profile o) (storeOf pr)) []
      [("get", ⟨[], [.int .i32]⟩)] = trapAll _ _ := by
  obtain ⟨tT, runT, hT⟩ := trap_engineRun h (Silmaril.Wasm.SingleThreaded.profile o)
  have nT := Silmaril.Proofs.Wasm.Component.Core3G.statusP_returned_no_step hT
  refine Silmaril.Proofs.Wasm.Component.Param.engineStrategyS_eq_trapAll rfl
    ⟨(storeOf pr), tT, runT, show flatStatus _ = _ by rw [hT]; rfl⟩ ?_
  intro s' t' run
  constructor
  · intro ys hys
    obtain ⟨r, hr⟩ : ∃ r, statusP (Silmaril.Wasm.SingleThreaded.profile o) s' t' = .returned r := by
      rcases Silmaril.Proofs.Wasm.Component.Core3G.flatStatus_eq_returned hys with ⟨vs, hv⟩ | hv
      · exact ⟨_, hv⟩
      · exact ⟨_, hv⟩
    have heq := Silmaril.Wasm.Game.reach_normal_unique run runT
      (Silmaril.Proofs.Wasm.Component.Core3G.statusP_returned_no_step hr) nT
    cases heq
    have : flatStatus (statusP (Silmaril.Wasm.SingleThreaded.profile o) (storeOf pr) tT) =
        .returned (.values ys) := hys
    rw [hT] at this
    cases this
  · intro hh args hc
    obtain ⟨h', args', hc'⟩ := Silmaril.Proofs.Wasm.Component.Core3G.flatStatus_eq_callout hc
    have heq := Silmaril.Wasm.Game.reach_normal_unique run runT
      (Silmaril.Proofs.Wasm.Component.Core3G.statusP_callout_no_step hc') nT
    cases heq
    rw [hT] at hc'
    cases hc'

theorem trapStartMod_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ none)] ∈
      engineStrategyS (core3P P) (startSI P trapStore) [] trapStartMod.exports :=
  trap_get trapPrep_ok P

theorem trapStartMod_eq_trapAll (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    engineStrategyS (core3P (Silmaril.Wasm.SingleThreaded.profile o))
      (startSI (Silmaril.Wasm.SingleThreaded.profile o) trapStore) []
      trapStartMod.exports = trapAll _ _ :=
  trap_eq_trapAll trapPrep_ok o
/-! ## The binaries, under `coreModSemLazyStart` -/

open Silmaril.Wasm.Component.Binary (coreModule coreModSem coreModSemLazyStart
  coreModSemLazyStart_sem_of_instS)

theorem startCM_prepOk : prepOk isSet (prepareE? {} (coreModule startCM) []) = true := by
  decide +kernel

theorem startCM_startOk : startOk (prepareE? {} (coreModule startCM) []) = true := by
  decide +kernel

theorem trapCM_prepOk : prepOk isUnreachable (prepareE? {} (coreModule trapCM) []) = true := by
  decide +kernel

theorem startCM_sem (P : Profile) :
    (coreModSemLazyStart P).sem startCM =
      engineStrategyS (core3P P) (startSI P (storeOf (prepareE? {} (coreModule startCM) []))) []
        [("get", ⟨[], [.int .i32]⟩)] :=
  coreModSemLazyStart_sem_of_instS P (instOfS_of_prepOk P startCM_prepOk _)

theorem trapCM_sem (P : Profile) :
    (coreModSemLazyStart P).sem trapCM =
      engineStrategyS (core3P P) (startSI P (storeOf (prepareE? {} (coreModule trapCM) []))) []
        [("get", ⟨[], [.int .i32]⟩)] :=
  coreModSemLazyStart_sem_of_instS P (instOfS_of_prepOk P trapCM_prepOk _)

theorem startCM_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ (some (.flat [Flat.i32 42])))] ∈ (coreModSemLazyStart P).sem startCM := by
  rw [startCM_sem]
  exact get_of startCM_prepOk startCM_startOk P

theorem trapCM_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ none)] ∈ (coreModSemLazyStart P).sem trapCM := by
  rw [trapCM_sem]
  exact trap_get trapCM_prepOk P

theorem trapCM_eq_trapAll (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    (coreModSemLazyStart (Silmaril.Wasm.SingleThreaded.profile o)).sem trapCM = trapAll _ _ := by
  rw [trapCM_sem]
  exact trap_eq_trapAll trapCM_prepOk o

/-! ## Under `engineSemS` and `engineSem` -/

theorem startMod_sem_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ (some (.flat [Flat.i32 42])))] ∈
      (engineSemS (core3P P) NumModule NumModule.mod).sem startMod := by
  rw [startMod_engineSemS]
  exact startMod_get P

theorem trapStartMod_sem_get (P : Profile) :
    [.inr (.ask getQ), .inr (.ans getQ none)] ∈
      (engineSemS (core3P P) NumModule NumModule.mod).sem trapStartMod := by
  rw [trapStartMod_engineSemS]
  exact trapStartMod_get P

theorem trapStartMod_sem_eq_trapAll (o : Silmaril.Wasm.SingleThreaded.GrowOracle) :
    (engineSemS (core3P (Silmaril.Wasm.SingleThreaded.profile o)) NumModule NumModule.mod).sem
      trapStartMod = trapAll _ _ := by
  rw [trapStartMod_engineSemS]
  exact trapStartMod_eq_trapAll o

theorem startMod_sem_ne_trapAll (P : Profile) :
    (engineSemS (core3P P) NumModule NumModule.mod).sem startMod ≠ trapAll _ _ := by
  intro h
  have hm := startMod_sem_get P
  rw [h] at hm
  exact Silmaril.Proofs.Wasm.Component.Param.two_some_not_mem_trapAll (n := 0) (k := 1) getQ _ hm

/-- An instance passing `prepOk isSet` and `startOk` is not `trapAll`. -/
theorem ne_trapAll_of {m : Silmaril.Wasm.Module} (h1 : prepOk isSet (prepareE? {} m []) = true)
    (h2 : startOk (prepareE? {} m []) = true) (P : Profile) :
    engineStrategyS (core3P P) (startSI P (storeOf (prepareE? {} m []))) []
      [("get", ⟨[], [.int .i32]⟩)] ≠ trapAll _ _ := by
  intro h
  have hm := get_of h1 h2 P
  rw [h] at hm
  exact Silmaril.Proofs.Wasm.Component.Param.two_some_not_mem_trapAll getQ _ hm

theorem startCM_ne_trapAll (P : Profile) : (coreModSemLazyStart P).sem startCM ≠ trapAll _ _ := by
  rw [startCM_sem]
  exact ne_trapAll_of startCM_prepOk startCM_startOk P

/-- Under the default `coreModSem` (start-free `engineSem`), the binary `startCM` has no
engine instance and traps on every question. -/
theorem startCM_coreModSem (P : Profile) : (coreModSem P).sem startCM = trapAll _ _ := by
  have h0 : instOfS (core3P P) (coreModule startCM : (core3P P).Module)
      (CoreModule.imports startCM) (CoreModule.exports startCM) =
        some (startSI P (storeOf (prepareE? {} (coreModule startCM) []))) :=
    instOfS_of_prepOk P startCM_prepOk _
  have h : instOf (core3P P) (coreModule startCM : (core3P P).Module)
      (CoreModule.imports startCM) (CoreModule.exports startCM) = none :=
    (Silmaril.Proofs.Wasm.Component.Param.instOf_eq _ _ _ _).trans (by rw [h0]; rfl)
  simp only [coreModSem, engineSem, h]

end Silmaril.Proofs.Wasm.Component.Param.StartCore3
