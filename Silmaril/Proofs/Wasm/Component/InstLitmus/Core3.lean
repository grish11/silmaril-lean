module

public import Silmaril.Wasm.Component.InstLitmus.Defs
public import Silmaril.Proofs.Wasm.Component.InstEngine.Basic
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkFloatWire
public import Silmaril.Proofs.Wasm.Component.Core3G.Sim

/-!
# Instantiation litmus modules on Core 3.0: instances and start runs

The instances (`prepareE?` against the host function of the import) are computed by kernel
evaluation of Boolean summaries (`decide +kernel`). The start runs are Core 3.0 runs built from
`Step` rules, for every profile:

* `callMod k`: `call_ref` enters the start function, `call 0` reaches the host function of the
  import with `i32 k` (`decompose?_fill`): a callout; resumed with `()`, the start function
  returns (`call_start_values`); resumed with anything else (a trap), it traps
  (`call_start_trap`);
* `trapMod`: `unreachable` traps (`trap_start`);
* `getMod`: no start function.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstLitmus

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.Engine.Core3 (prepareE? instExports)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Game (FnType Reach ResultAt statusP)
open Silmaril.Wasm.SingleThreaded (hostArity? decompose?)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Component.Reference.Litmus (steps_frame_label reach_of_steps
  hostArity?_code)

/-- Runs of an engine. -/
local notation "ESteps" => Silmaril.Wasm.Component.Engine.CoreEngine.Steps

/-! ## Instances -/

/-- The function type `[] → []`. -/
abbrev unitFn : FnType := ⟨[], []⟩

/-- The function type `[i32] → []` of the import. -/
abbrev fFn : FnType := ⟨[.num (.int .i32)], []⟩

/-- The function type `[] → [i32]` of `get`. -/
abbrev getFn : FnType := ⟨[], [.num (.int .i32)]⟩

/-- The host function of the import, allocated in the empty store. -/
def hostS : Store Nat × Nat :=
  Silmaril.Wasm.SingleThreaded.allocHost ({} : Store Nat) (v1Type fFt) 0

/-- The function instance has no locals and the body `i32.const k; call x` with `x = 0`, and
its module's function `0` is at address `0`. -/
def isCall (k : BitVec 32) (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.intConst .i32 v, .call x]⟩ =>
    v == k && x.toNat == 0 && fi.module.funcs[0]? == some 0
  | _ => false

/-- The function instance has no locals and the body `unreachable`. -/
def isUnreachable (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.unreachable]⟩ => true
  | _ => false

/-- The checks on the store of `callMod k`. -/
def callStoreOk (k : BitVec 32) (s : Store Nat) : Bool :=
  hostArity? s 0 == some (0, 1) &&
    (match s.funcs[0]? with
     | some f0 => FnType.ofDefType? f0.type == some fFn
     | none => false) &&
    (match s.funcs[1]? with
     | some f1 => FnType.ofDefType? f1.type == some unitFn && isCall k f1
     | none => false)

/-- A prepared instance whose start function is at address `a` and whose store passes `B`. -/
def prepOk (a : Nat) (B : Store Nat → Bool) : Option (Store Nat × ModuleInst × Option Nat) → Bool
  | some (s, _, some a') => a' == a && B s
  | _ => false

/-- The store of a prepared instance. -/
def storeOf : Option (Store Nat × ModuleInst × Option Nat) → Store Nat
  | some (s, _, _) => s
  | none => {}

theorem prepOk_eq {a : Nat} {B : Store Nat → Bool} :
    ∀ {o : Option (Store Nat × ModuleInst × Option Nat)}, prepOk a B o = true →
      ∃ inst, o = some (storeOf o, inst, some a) ∧ B (storeOf o) = true
  | some (s, inst, some a'), h => by
    simp only [prepOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact ⟨inst, rfl, h⟩
  | some (_, _, none), h => nomatch h
  | none, h => nomatch h

/-- The prepared instance of `callCore3 k`. -/
def callPrep (k : BitVec 32) : Option (Store Nat × ModuleInst × Option Nat) :=
  prepareE? hostS.1 (callCore3 k) [.func hostS.2]

theorem callPrep_one : prepOk 1 (callStoreOk 1) (callPrep 1) = true := by decide +kernel

theorem callPrep_two : prepOk 1 (callStoreOk 2) (callPrep 2) = true := by decide +kernel

/-- The instance of `callMod k` before its start function. -/
def callI (P : Profile) (k : BitVec 32) : IInstance (core3P P) :=
  ⟨storeOf (callPrep k), [], some (1 : Nat)⟩

theorem instOfI_call (P : Profile) {k : BitVec 32}
    (h : prepOk 1 (callStoreOk k) (callPrep k) = true) :
    instOfI (core3P P) (callMod k).mod (callMod k).imports (callMod k).exports =
      some (callI P k) := by
  obtain ⟨inst, hp, -⟩ := prepOk_eq h
  have hp' : (core3P P).prepare? (H := Nat) hostS.1 (callCore3 k) [.func hostS.2] =
      some (storeOf (callPrep k), inst, some (1 : Nat)) := hp
  have ha : allocHosts (core3P P) ((core3P P).empty Nat) 0 [("f", fFt)] =
      (hostS.1, [hostS.2]) := rfl
  have he : exportAddrs (core3P P) inst [] = some [] := rfl
  unfold instOfI
  simp only [callMod, ha]
  erw [hp']
  simp only [he, Option.map_some]
  rfl

/-- The checks on the store of `trapMod`. -/
def trapStoreOk (s : Store Nat) : Bool :=
  match s.funcs[0]? with
  | some f0 => FnType.ofDefType? f0.type == some unitFn && isUnreachable f0
  | none => false

/-- The prepared instance of `trapCore3`. -/
def trapPrep : Option (Store Nat × ModuleInst × Option Nat) := prepareE? {} trapCore3 []

theorem trapPrep_ok : prepOk 0 trapStoreOk trapPrep = true ∧
    ((match trapPrep with
      | some (_, inst, _) => (instExports inst).lookup "get" == some (.func 1)
      | none => false) = true) := by
  decide +kernel

/-- The instance of `trapMod` before its start function. -/
def trapI (P : Profile) : IInstance (core3P P) := ⟨storeOf trapPrep, [(1 : Nat)], some (0 : Nat)⟩

theorem instOfI_trap (P : Profile) :
    instOfI (core3P P) trapMod.mod trapMod.imports trapMod.exports = some (trapI P) := by
  obtain ⟨inst, hp, -⟩ := prepOk_eq trapPrep_ok.1
  have hl : (instExports inst).lookup "get" = some (.func 1) := by
    have h2 := trapPrep_ok.2
    rw [show trapPrep = _ from hp] at h2
    simpa only [beq_iff_eq] using h2
  have hp' : (core3P P).prepare? (H := Nat) ((core3P P).empty Nat) trapCore3 [] =
      some (storeOf trapPrep, inst, some (0 : Nat)) := hp
  have he : exportAddrs (core3P P) inst [("get", getFt)] = some [(1 : Nat)] := by
    unfold exportAddrs
    show List.mapM (fun x => ((instExports inst).lookup x.1).bind
      Silmaril.Wasm.Component.Engine.Core3.asFunc?) [("get", getFt)] = some [1]
    simp [hl, Silmaril.Wasm.Component.Engine.Core3.asFunc?]
  unfold instOfI
  simp only [trapMod, allocHosts, List.map_nil, hp', he]
  rfl

/-- The prepared instance of `getCore3`. -/
def getPrep : Option (Store Nat × ModuleInst × Option Nat) := prepareE? {} getCore3 []

theorem getPrep_ok : (match getPrep with
    | some (_, inst, none) => (instExports inst).lookup "get" == some (.func 0)
    | _ => false) = true := by
  decide +kernel

/-- The instance of `getMod`: no start function. -/
def getI (P : Profile) : IInstance (core3P P) := ⟨storeOf getPrep, [(0 : Nat)], none⟩

theorem instOfI_get (P : Profile) :
    instOfI (core3P P) getMod.mod getMod.imports getMod.exports = some (getI P) := by
  have h := getPrep_ok
  obtain ⟨s, inst, hp, hl⟩ : ∃ s inst, getPrep = some (s, inst, none) ∧
      (instExports inst).lookup "get" = some (.func 0) := by
    revert h
    cases getPrep with
    | none => intro h; cases h
    | some x =>
      obtain ⟨s, inst, st⟩ := x
      cases st with
      | some _ => intro h; cases h
      | none => intro h; exact ⟨s, inst, rfl, by simpa only [beq_iff_eq] using h⟩
  have hs : storeOf getPrep = s := by rw [hp]; rfl
  have hp' : (core3P P).prepare? (H := Nat) ((core3P P).empty Nat) getCore3 [] =
      some (s, inst, none) := hp
  have he : exportAddrs (core3P P) inst [("get", getFt)] = some [(0 : Nat)] := by
    unfold exportAddrs
    show List.mapM (fun x => ((instExports inst).lookup x.1).bind
      Silmaril.Wasm.Component.Engine.Core3.asFunc?) [("get", getFt)] = some [0]
    simp [hl, Silmaril.Wasm.Component.Engine.Core3.asFunc?]
  unfold instOfI
  simp only [getMod, allocHosts, List.map_nil, hp', he]
  rw [getI, hs]
  rfl

/-! ## Runs -/

theorem isCall_code {k : BitVec 32} {fi : FuncInst Nat} (h : isCall k fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.FuncIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.intConst .i32 k, .call x] ∧ x.toNat = 0 ∧
      fi.module.funcs[0]? = some 0 := by
  unfold isCall at h
  split at h
  next t v x hc =>
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hv, hx⟩, hm⟩ := h
    obtain rfl : v = k := eq_of_beq hv
    exact ⟨_, x, hc, rfl, rfl, beq_iff_eq.1 hx, beq_iff_eq.1 hm⟩
  next => cases h

theorem isUnreachable_code {fi : FuncInst Nat} (h : isUnreachable fi = true) :
    ∃ code : Silmaril.Wasm.Func, fi.code = .wasm code ∧ code.body = [.unreachable] := by
  unfold isUnreachable at h
  split at h
  next t hc => exact ⟨_, hc, rfl⟩
  next => cases h

/-- The facts `callStoreOk` records. -/
theorem callStore_facts {k : BitVec 32} {s : Store Nat} (h : callStoreOk k s = true) :
    ∃ f0 f1 : FuncInst Nat, hostArity? s 0 = some (0, 1) ∧ s.funcs[0]? = some f0 ∧
      FnType.ofDefType? f0.type = some fFn ∧ s.funcs[1]? = some f1 ∧
      FnType.ofDefType? f1.type = some unitFn ∧ isCall k f1 = true := by
  unfold callStoreOk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨ha, h0⟩, h1⟩ := h
  split at h0
  next f0 hf0 =>
    split at h1
    next f1 hf1 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at h0 h1
      exact ⟨f0, f1, ha, hf0, h0, hf1, h1.1, h1.2⟩
    next => cases h1
  next => cases h0

theorem statusP_of_decompose {P : Profile} {s : Store Nat}
    {t : Silmaril.Wasm.SingleThreaded.Thread}
    (n₁ : ¬ ∃ vs, (t.config s).code = vals vs) (n₂ : ¬ (t.config s).code = [.trap])
    (n₃ : ¬ ∃ a, (t.config s).code = throwing a)
    {E : Silmaril.Wasm.SingleThreaded.Ctx} {a : Nat} {c : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val}
    (hd : decompose? s (t.config s).code = some (E, a, c, args)) :
    statusP P s t = .callout c args := by
  unfold statusP
  dsimp only
  split_ifs
  all_goals rw [hd]

/-- The callout context of a start function: its frame and its body's label. -/
def startCtx (F : Frame) : Silmaril.Wasm.SingleThreaded.Ctx :=
  .frame [] 0 F (.label [] 0 [] (.top [] []) []) []

theorem not_vals_frame {n : Nat} {F : Frame} {b : List Admin} :
    ¬ ∃ vs, ([.frame n F b] : List Admin) = vals vs := by
  rintro ⟨vs, h⟩
  have h' := congrArg Silmaril.Wasm.SingleThreaded.splitVals h
  rw [Silmaril.Wasm.SingleThreaded.splitVals_vals] at h'
  simp [Silmaril.Wasm.SingleThreaded.splitVals, Admin.val?] at h'

theorem engineSteps_of_steps {P : Profile} {s : Store Nat}
    {t : Silmaril.Wasm.SingleThreaded.Thread} {s' : Store Nat} {F : Frame} {code : List Admin}
    (h : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost (t.config s) ⟨s', F, code⟩) :
    ∃ t', ESteps (core3P P) (s, t) (s', t') ∧ t'.config s' = ⟨s', F, code⟩ := by
  obtain ⟨s'', t', hr, hd⟩ := reach_of_steps h
  have hs : s'' = s' := by
    have h₁ : (t'.config s'').store = s'' := by cases t' <;> rfl
    rw [← h₁, hd]
  subst hs
  exact ⟨t', hr, hd⟩

/-- **The start function of `callMod k` calls the import with `i32 k`**, for every profile; resumed
with `()` it returns, resumed with a trap it traps. -/
theorem call_start {P : Profile} {k : BitVec 32} {s : Store Nat} (h : callStoreOk k s = true) :
    ∃ t, ESteps (core3P P) (s, (core3P P).invoke (1 : Nat) []) (s, t) ∧
      (core3P P).status s t = .callout 0 [Flat.i32 k] ∧
      (∃ t', ESteps (core3P P) (s, (core3P P).resume s t (.values [])) (s, t') ∧
        (core3P P).status s t' = .returned (.values [])) ∧
      (∃ t', ESteps (core3P P) (s, (core3P P).resume s t .trap) (s, t') ∧
        (core3P P).status s t' = .returned .trap) := by
  obtain ⟨f0, f1, harity, hf0, hty0, hf1, hty1, hc⟩ := callStore_facts h
  obtain ⟨code, x, hcode, hloc, hbody, hx, hm⟩ := isCall_code hc
  obtain ⟨f0', hf0', hcode0⟩ := hostArity?_code harity
  have hfh : f0' = f0 := Option.some_injective _ (hf0'.symm.trans hf0)
  subst hfh
  have he1 : Expand f1.type unitFn.toComp := FnType.expand_of_ofDefType? hty1
  have he0 : Expand f0'.type fFn.toComp := FnType.expand_of_ofDefType? hty0
  let F := Frame.forCall f1.module [] code.locals
  have s₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s 1 [])
      ⟨s, {}, [.frame 0 F [.label 0 [] (expression code.body)]]⟩ :=
    .callRefFunc (vs := []) (c := .callRefType ((s.funcs[1]?.map FuncInst.type).getD default))
      trivial hf1 he1 rfl hcode
  have hxF : F.module.funcs[x.toNat]? = some 0 := by rw [hx]; exact hm
  have a₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
      ⟨s, F, vals [Val.i32 k] ++ [.plain (.call x)] ++ []⟩
      ⟨s, F, vals [Val.i32 k] ++ [.ref (.func 0), .callRefType f0'.type] ++ []⟩ :=
    .ctxtInstrs (.call hxF hf0) (.inl (by simp))
  have s₂ : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost ⟨s, F, expression code.body⟩
      ⟨s, F, vals [Val.i32 k] ++ [.ref (.func 0), .callRefType f0'.type] ++ []⟩ := by
    rw [hbody]
    exact .single a₁
  have run : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
      ((Silmaril.Wasm.SingleThreaded.Thread.invoke 1 []).config s)
      ⟨s, {}, (startCtx F).fill (vals [Val.i32 k] ++ [.ref (.func 0), .callRefType f0'.type])⟩ :=
    (Relation.ReflTransGen.single s₁).trans (steps_frame_label s₂)
  obtain ⟨t₁, hr₁, hd₁⟩ := engineSteps_of_steps run
  have hdec : decompose? s (t₁.config s).code = some (startCtx F, 0, 0, [Val.i32 k]) := by
    rw [hd₁]
    exact Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill _ trivial hf0 he0
      (Ty.length_ofList (fFn.params.map Silmaril.Wasm.Game.ScalarType.toC)).symm hcode0
  have hcode₁ : (t₁.config s).code = [.frame 0 F [.label 0 [] (vals [Val.i32 k] ++
      [.ref (.func 0), .callRefType f0'.type])]] := by rw [hd₁]; rfl
  have hst : statusP P s t₁ = .callout 0 [Val.i32 k] :=
    statusP_of_decompose (P := P) (s := s) (t := t₁)
      (by rw [hcode₁]; exact not_vals_frame)
      (by rw [hcode₁]; simp)
      (by rw [hcode₁]; rintro ⟨a, ha⟩; simp [throwing] at ha)
      hdec
  have hfr : (t₁.config s).frame = {} := by rw [hd₁]
  have hres : ∀ r, (core3P P).resume s t₁ r = .active {}
      [.frame 0 F [.label 0 [] (Silmaril.Wasm.Component.Engine.Core3.toCR r).toAdmin]] := by
    intro r
    show Silmaril.Wasm.SingleThreaded.resume s t₁ _ = _
    unfold Silmaril.Wasm.SingleThreaded.resume
    simp only [hdec, hfr, startCtx, Silmaril.Wasm.SingleThreaded.Ctx.fill, Silmaril.Wasm.SingleThreaded.vals_nil,
      List.nil_append, List.append_nil]
  refine ⟨t₁, hr₁, ?_, ?_, ?_⟩
  · show Silmaril.Wasm.Component.Reference.flatStatus (statusP P s t₁) = _
    rw [hst]
    rfl
  · have run₂ : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
        ((Silmaril.Wasm.SingleThreaded.Thread.active {}
          [.frame 0 F [.label 0 [] (vals [])]]).config s) ⟨s, {}, vals []⟩ :=
      (Relation.ReflTransGen.single (.ctxtFrame .labelVals)).tail (.frameVals rfl)
    obtain ⟨t₂, hr₂, hd₂⟩ := engineSteps_of_steps run₂
    refine ⟨t₂, (hres _).symm ▸ hr₂, ?_⟩
    show Silmaril.Wasm.Component.Reference.flatStatus (statusP P s t₂) = _
    rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_values (P := P) (s := s) (t := t₂)
      (vs := []) (by rw [hd₂])]
    rfl
  · have run₂ : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
        ((Silmaril.Wasm.SingleThreaded.Thread.active {}
          [.frame 0 F [.label 0 [] [.trap]]]).config s) ⟨s, {}, [.trap]⟩ :=
      (Relation.ReflTransGen.single (.ctxtFrame .trapLabel)).tail .trapFrame
    obtain ⟨t₂, hr₂, hd₂⟩ := engineSteps_of_steps run₂
    refine ⟨t₂, (hres _).symm ▸ hr₂, ?_⟩
    show Silmaril.Wasm.Component.Reference.flatStatus (statusP P s t₂) = _
    rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_trap (P := P) (s := s) (t := t₂)
      (by rw [hd₂])]
    rfl

/-- **The start function of `trapMod` traps**, for every profile. -/
theorem trap_start {P : Profile} {s : Store Nat} (h : trapStoreOk s = true) :
    ∃ t, ESteps (core3P P) (s, (core3P P).invoke (0 : Nat) []) (s, t) ∧
      (core3P P).status s t = .returned .trap := by
  unfold trapStoreOk at h
  split at h
  next f0 hf0 =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hty, hu⟩ := h
    obtain ⟨code, hcode, hbody⟩ := isUnreachable_code hu
    have he : Expand f0.type unitFn.toComp := FnType.expand_of_ofDefType? hty
    let F := Frame.forCall f0.module [] code.locals
    have s₁ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost (invoke s 0 [])
        ⟨s, {}, [.frame 0 F [.label 0 [] (expression code.body)]]⟩ :=
      .callRefFunc (vs := []) (c := .callRefType ((s.funcs[0]?.map FuncInst.type).getD default))
        trivial hf0 he rfl hcode
    have s₂ : Step P Silmaril.Wasm.SingleThreaded.Det.noHost
        ⟨s, F, expression code.body⟩ ⟨s, F, [.trap]⟩ := by
      rw [hbody]
      exact .parametric .unreachable
    have s₃ := steps_frame_label (f := {}) (n := 0) (m := 0) (cont := [])
      (Relation.ReflTransGen.single s₂)
    have run : Steps P Silmaril.Wasm.SingleThreaded.Det.noHost
        ((Silmaril.Wasm.SingleThreaded.Thread.invoke 0 []).config s) ⟨s, {}, [.trap]⟩ :=
      (Relation.ReflTransGen.single s₁).trans
        ((s₃.tail (.ctxtFrame .trapLabel)).tail .trapFrame)
    obtain ⟨t, hr, hd⟩ := engineSteps_of_steps run
    refine ⟨t, hr, ?_⟩
    show Silmaril.Wasm.Component.Reference.flatStatus (statusP P s t) = _
    rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_trap (P := P) (s := s) (t := t)
      (by rw [hd])]
    rfl
  next => cases h

end Silmaril.Proofs.Wasm.Component.InstLitmus
