module

public import Silmaril.Proofs.Wasm.Component.InstLitmus.Core3

/-!
# The global litmus module on Core 3.0: instance and runs

`globMod` (`Silmaril.Wasm.Component.InstLitmus`): no imports, a mutable `i32` global, a start
function `i32.const 42; global.set 0`, an export `get` returning `global.get 0`. The instance
(`prepareE?`) is computed by kernel evaluation of a Boolean summary (`decide +kernel`); the runs
are Core 3.0 runs built from `Step` rules, for every profile:

* `glob_start`: the start function returns, leaving the store with the global set to `42`;
* `glob_get`: from that store, `get` returns `42`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstLitmus

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.Engine.Core3 (prepareE? instExports)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Game (FnType)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Component.Reference.Litmus (steps_frame_label)

/-- Runs of an engine. -/
local notation "ESteps" => Silmaril.Wasm.Component.Engine.CoreEngine.Steps

/-- The function instance has no locals and the body `i32.const 42; global.set 0`. -/
def isGlobSet (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.intConst .i32 v, .globalSet x]⟩ => v == 42 && x.toNat == 0
  | _ => false

/-- The function instance has no locals and the body `global.get 0`. -/
def isGlobGet (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.globalGet x]⟩ => x.toNat == 0
  | _ => false

/-- The checks on the store of `globMod`: the start function at `0`, `get` at `1`, both in a
module whose global `0` is at address `0`, which the store has. -/
def globStoreOk (s : Store Nat) : Bool :=
  match s.funcs[0]?, s.funcs[1]? with
  | some f0, some f1 =>
    FnType.ofDefType? f0.type == some unitFn && isGlobSet f0 &&
      FnType.ofDefType? f1.type == some getFn && isGlobGet f1 &&
      f0.module.globals[0]? == some 0 && f1.module.globals[0]? == some 0 &&
      (s.globals[0]?).isSome
  | _, _ => false

/-- The prepared instance of `globCore3`. -/
def globPrep : Option (Store Nat × ModuleInst × Option Nat) := prepareE? {} globCore3 []

theorem globPrep_ok : prepOk 0 globStoreOk globPrep = true ∧
    ((match globPrep with
      | some (_, inst, _) => (instExports inst).lookup "get" == some (.func 1)
      | none => false) = true) := by
  decide +kernel

/-- The instance of `globMod` before its start function. -/
def globI (P : Profile) : IInstance (core3P P) := ⟨storeOf globPrep, [(1 : Nat)], some (0 : Nat)⟩

theorem instOfI_glob (P : Profile) :
    instOfI (core3P P) globMod.mod globMod.imports globMod.exports = some (globI P) := by
  obtain ⟨inst, hp, -⟩ := prepOk_eq globPrep_ok.1
  have hl : (instExports inst).lookup "get" = some (.func 1) := by
    have h2 := globPrep_ok.2
    rw [show globPrep = _ from hp] at h2
    simpa only [beq_iff_eq] using h2
  have hp' : (core3P P).prepare? (H := Nat) ((core3P P).empty Nat) globCore3 [] =
      some (storeOf globPrep, inst, some (0 : Nat)) := hp
  have he : exportAddrs (core3P P) inst [("get", getFt)] = some [(1 : Nat)] := by
    unfold exportAddrs
    show List.mapM (fun x => ((instExports inst).lookup x.1).bind
      Silmaril.Wasm.Component.Engine.Core3.asFunc?) [("get", getFt)] = some [1]
    simp [hl, Silmaril.Wasm.Component.Engine.Core3.asFunc?]
  unfold instOfI
  simp only [globMod, allocHosts, List.map_nil, hp', he]
  rfl

theorem isGlobSet_code {fi : FuncInst Nat} (h : isGlobSet fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.GlobalIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.intConst .i32 42, .globalSet x] ∧ x.toNat = 0 := by
  unfold isGlobSet at h
  split at h
  next t v x hc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hx⟩ := h
    exact ⟨_, x, hc, rfl, rfl, hx⟩
  next => cases h

theorem isGlobGet_code {fi : FuncInst Nat} (h : isGlobGet fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.GlobalIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.globalGet x] ∧ x.toNat = 0 := by
  unfold isGlobGet at h
  split at h
  next t x hc => exact ⟨_, x, hc, rfl, rfl, beq_iff_eq.1 h⟩
  next => cases h

/-- The facts `globStoreOk` records. -/
theorem globStore_facts {s : Store Nat} (h : globStoreOk s = true) :
    ∃ (f0 f1 : FuncInst Nat) (g : GlobalInst), s.funcs[0]? = some f0 ∧
      FnType.ofDefType? f0.type = some unitFn ∧ isGlobSet f0 = true ∧ s.funcs[1]? = some f1 ∧
      FnType.ofDefType? f1.type = some getFn ∧ isGlobGet f1 = true ∧
      f0.module.globals[0]? = some 0 ∧ f1.module.globals[0]? = some 0 ∧
      s.globals[0]? = some g := by
  unfold globStoreOk at h
  split at h
  next f0 f1 h0 h1 =>
    simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨⟨⟨⟨ht0, hs0⟩, ht1⟩, hg1⟩, hm0⟩, hm1⟩, g, hg⟩ := h
    exact ⟨f0, f1, g, h0, ht0, hs0, h1, ht1, hg1, hm0, hm1, hg⟩
  next => cases h

/-- The store after the start function. -/
def globAfter (s : Store Nat) : Store Nat := s.setGlobal 0 (Val.i32 42)

/-- **The start function of `globMod` returns**, leaving the global at `42`, for every
profile. -/
theorem glob_start {P : Profile} {s : Store Nat} (h : globStoreOk s = true) :
    ∃ t, ESteps (core3P P) (s, (core3P P).invoke (0 : Nat) []) (globAfter s, t) ∧
      (core3P P).status (globAfter s) t = .returned (.values []) := by
  obtain ⟨f0, f1, g, hf0, hty0, hs0, -, -, -, hm0, -, hg⟩ := globStore_facts h
  obtain ⟨code, x, hcode, hloc, hbody, hx⟩ := isGlobSet_code hs0
  have he : Expand f0.type unitFn.toComp := FnType.expand_of_ofDefType? hty0
  let F := Frame.forCall f0.module [] code.locals
  have s₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s 0 [])
      ⟨s, {}, [.frame 0 F [.label 0 [] (expression code.body)]]⟩ :=
    .callRefFunc (vs := []) (c := .callRefType ((s.funcs[0]?.map FuncInst.type).getD default))
      trivial hf0 he rfl hcode
  have hgl : s.global? F x = some (0, g) := by
    simp only [Store.global?, F, Frame.forCall, hx, hm0, Option.bind_eq_bind,
      Option.bind_some, hg]
    rfl
  have s₂ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost ⟨s, F, expression code.body⟩
      ⟨globAfter s, F, []⟩ := by
    rw [hbody]
    exact .variable (.globalSet (v := Val.i32 42) hgl)
  have s₃ := steps_frame_label (f := {}) (n := 0) (m := 0) (cont := [])
    (Relation.ReflTransGen.single s₂)
  have run : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ((Silmaril.Wasm.SingleThreaded.Thread.invoke 0 []).config s) ⟨globAfter s, {}, vals []⟩ :=
    (Relation.ReflTransGen.single s₁).trans
      ((s₃.tail (.ctxtFrame (.labelVals (vs := [])))).tail (.frameVals rfl))
  obtain ⟨t, hr, hd⟩ := engineSteps_of_steps run
  refine ⟨t, hr, ?_⟩
  show Silmaril.Wasm.Component.Reference.flatStatus
    (Silmaril.Wasm.Game.statusP P (globAfter s) t) = _
  rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_values (P := P) (s := globAfter s) (t := t)
    (vs := []) (by rw [hd])]
  rfl

/-- **After the start function, `get` returns `42`**, for every profile. -/
theorem glob_get {P : Profile} {s : Store Nat} (h : globStoreOk s = true) :
    ∃ t, ESteps (core3P P) (globAfter s, (core3P P).invoke (1 : Nat) []) (globAfter s, t) ∧
      (core3P P).status (globAfter s) t = .returned (.values [Flat.i32 42]) := by
  obtain ⟨f0, f1, g, -, -, -, hf1, hty1, hs1, -, hm1, hg⟩ := globStore_facts h
  obtain ⟨code, x, hcode, hloc, hbody, hx⟩ := isGlobGet_code hs1
  have he : Expand f1.type getFn.toComp := FnType.expand_of_ofDefType? hty1
  have hf1' : (globAfter s).funcs[1]? = some f1 := hf1
  let F := Frame.forCall f1.module [] code.locals
  have s₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke (globAfter s) 1 [])
      ⟨globAfter s, {}, [.frame 1 F [.label 1 [] (expression code.body)]]⟩ :=
    .callRefFunc (vs := [])
      (c := .callRefType (((globAfter s).funcs[1]?.map FuncInst.type).getD default))
      trivial hf1' he rfl hcode
  have hgl : (globAfter s).global? F x =
      some (0, { g with value := Val.i32 42 }) := by
    simp only [Store.global?, F, Frame.forCall, hx, hm1, globAfter, Store.setGlobal,
      Option.bind_eq_bind, Option.bind_some, List.getElem?_modify, hg, Option.map_eq_map,
      Option.map_some, ↓reduceIte]
    rfl
  have s₂ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost ⟨globAfter s, F, expression code.body⟩
      ⟨globAfter s, F, vals [Val.i32 42]⟩ := by
    rw [hbody]
    exact .variable (.globalGet hgl)
  have s₃ := steps_frame_label (f := {}) (n := 1) (m := 1) (cont := [])
    (Relation.ReflTransGen.single s₂)
  have run : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ((Silmaril.Wasm.SingleThreaded.Thread.invoke 1 []).config (globAfter s))
      ⟨globAfter s, {}, vals [Val.i32 42]⟩ :=
    (Relation.ReflTransGen.single s₁).trans
      ((s₃.tail (.ctxtFrame .labelVals)).tail (.frameVals rfl))
  obtain ⟨t, hr, hd⟩ := engineSteps_of_steps run
  refine ⟨t, hr, ?_⟩
  show Silmaril.Wasm.Component.Reference.flatStatus
    (Silmaril.Wasm.Game.statusP P (globAfter s) t) = _
  rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_values (P := P) (s := globAfter s) (t := t)
    (vs := [Val.i32 42]) (by rw [hd])]
  rfl

end Silmaril.Proofs.Wasm.Component.InstLitmus
