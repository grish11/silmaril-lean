module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR.Rounds
public import Silmaril.Proofs.Wasm.Component.Reference.LitmusLinkFloatWire
public import Silmaril.Wasm.Component.Reference.LinkedSession.Defs

/-!
# The IR side of the linked fixture `linkedC`

* The exporter A (`setGetCore`): its instance (`sgFacts`, `sg_isInst`; kernel evaluation of a
  Boolean summary of the instantiation), the call `set` (`set_run`: `i32.const 1`,
  `global.set 0`, `unreachable`, the trap leaving `sgStore₁`, whose global is `1`), a trapped
  call of the specification (`set_trapAt`), and the call `get` from every store with A's
  functions and one global (`get_run`, `get_retAt`). Every profile.
* The importer B (`LinkedSession.pokePeekCore`): its instance (`ppFacts`, `pp_isInst`), the
  callout of an export call at its import (`pp_callout`), the play of `poke` whose import call
  `set` is answered by a trap (`poke_path`, through `trapImport_path`) and of `peek` whose
  import call `get` is answered `y` (`peek_path`), with their `ImpRel`s (`set_impRel` by
  `impRel_trap`, `get_impRel`). Every profile.
* The linked plays (`linkedC_ir_session`, `linkedC_ir_peek_fresh`): through `linked2_sessToIR`,
  with the exporter run `set` trapped then `get` from the trap store (`ExpRunT`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.LinkedSession (setGetCore setGetS pokePeekI linkedC unitTy
  u32Ty)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

/-- The scalar type `() -> ()`. -/
abbrev unitFn : FnType := ⟨[], []⟩

/-- The scalar type `() -> (i32)`. -/
abbrev i32Fn : FnType := ⟨[], [.num (.int .i32)]⟩

/-! ## Lists from their images -/

theorem single_of_map {α β : Type} {g : α → β} {b : β} :
    ∀ {l : List α}, l.map g = [b] → ∃ x, l = [x] ∧ g x = b
  | [x], h => ⟨x, rfl, by simpa using h⟩
  | [], h => nomatch h
  | _ :: _ :: _, h => by simp at h

theorem pair_of_map {α β : Type} {g : α → β} {b₁ b₂ : β} :
    ∀ {l : List α}, l.map g = [b₁, b₂] → ∃ x y, l = [x, y] ∧ g x = b₁ ∧ g y = b₂
  | [x, y], h => by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨x, y, rfl, h.1, h.2⟩
  | [], h => nomatch h
  | [_], h => by simp at h
  | _ :: _ :: _ :: _, h => by simp at h

theorem four_of_map {α β : Type} {g : α → β} {b₁ b₂ b₃ b₄ : β} :
    ∀ {l : List α}, l.map g = [b₁, b₂, b₃, b₄] →
      ∃ x₁ x₂ x₃ x₄, l = [x₁, x₂, x₃, x₄] ∧ g x₁ = b₁ ∧ g x₂ = b₂ ∧ g x₃ = b₃ ∧ g x₄ = b₄
  | [x₁, x₂, x₃, x₄], h => by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨x₁, x₂, x₃, x₄, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2⟩
  | [], h => nomatch h
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [_, _, _], h => by simp at h
  | _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

/-! ## The exporter A -/

/-- The store of the instance of `setGetCore`. -/
def sgStore : Store Nat :=
  match instantiateOnce? (importStore []) setGetCore [] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `setGetCore`. -/
def sgInst : ScalarInstance where
  imports := []
  exports := [unitFn, i32Fn]
  addrs := [0, 1]
  store := sgStore

/-- The function instance has the body `i32.const 1; global.set 0; unreachable`, no locals, and
its module's global `0` is at address `0`. -/
def isSet (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.intConst .i32 b, .globalSet x, .unreachable]⟩ =>
    b == 1 && x.toNat == 0 && fi.module.globals == [0]
  | _ => false

/-- The function instance has the body `global.get 0`, no locals, and its module's global `0`
is at address `0`. -/
def isGet (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.globalGet x]⟩ => x.toNat == 0 && fi.module.globals == [0]
  | _ => false

/-- What the summary records of a function instance of A. -/
def sgInfo (fi : FuncInst Nat) : Option FnType × Bool × Bool :=
  (FnType.ofDefType? fi.type, isSet fi, isGet fi)

/-- The checks on the instantiated store and frame. -/
def sgBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [0, 1] &&
    s.funcs.map sgInfo == [(some unitFn, true, false), (some i32Fn, false, true)] &&
    s.globals.map (·.value) == [Val.i32 0]

/-- The Boolean summary of the instantiation of `setGetCore`. -/
def sgSummary : Bool :=
  ((validate? setGetCore).map (·.imports.length) == some 0) &&
    Litmus.runOk sgBody (instantiateOnce? (importStore []) setGetCore [])

theorem sgSummary_eq : sgSummary = true := by decide +kernel

theorem isSet_code {fi : FuncInst Nat} (h : isSet fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.GlobalIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.intConst .i32 1, .globalSet x, .unreachable] ∧
      x.toNat = 0 ∧ fi.module.globals = [0] := by
  unfold isSet at h
  split at h
  next t b x hc =>
    have h' : (b = 1 ∧ x.toNat = 0) ∧ fi.module.globals = [0] := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    obtain ⟨⟨rfl, hx⟩, hm⟩ := h'
    exact ⟨_, x, hc, rfl, rfl, hx, hm⟩
  next => cases h

theorem isGet_code {fi : FuncInst Nat} (h : isGet fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.GlobalIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.globalGet x] ∧ x.toNat = 0 ∧ fi.module.globals = [0] := by
  unfold isGet at h
  split at h
  next t x hc =>
    have h' : x.toNat = 0 ∧ fi.module.globals = [0] := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    exact ⟨_, x, hc, rfl, rfl, h'.1, h'.2⟩
  next => cases h

/-- The facts the summary records. -/
structure SgFacts : Prop where
  valid : ∃ mt, validate? setGetCore = some mt ∧ mt.imports = []
  inst : ∃ f : Frame, instantiateOnce? (importStore []) setGetCore [] = some (sgStore, f, none) ∧
    exportFuncAddrs f.module = [0, 1]
  funcs : ∃ fs fg : FuncInst Nat, sgStore.funcs = [fs, fg] ∧
    FnType.ofDefType? fs.type = some unitFn ∧ FnType.ofDefType? fg.type = some i32Fn ∧
    isSet fs = true ∧ isGet fg = true
  globals : ∃ g : GlobalInst, sgStore.globals = [g] ∧ g.value = Val.i32 0

theorem sgFacts : SgFacts := by
  have h' : (validate? setGetCore).map (·.imports.length) = some 0 ∧
      Litmus.runOk sgBody (instantiateOnce? (importStore []) setGetCore []) = true := by
    simpa only [sgSummary, Bool.and_eq_true, beq_iff_eq] using sgSummary_eq
  obtain ⟨mt, hmt, hlen⟩ := Option.map_eq_some_iff.mp h'.1
  obtain ⟨s, f, hrun, hb⟩ := Litmus.runOk_eq h'.2
  have hs : sgStore = s := by simp only [sgStore, hrun]
  have hb' : (exportFuncAddrs f.module = [0, 1] ∧
      s.funcs.map sgInfo = [(some unitFn, true, false), (some i32Fn, false, true)]) ∧
      s.globals.map (·.value) = [Val.i32 0] := by
    simpa only [sgBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨fs, fg, hfs, h₁, h₂⟩ := pair_of_map hb'.1.2
  obtain ⟨g, hg, hgv⟩ := single_of_map hb'.2
  simp only [sgInfo, Prod.mk.injEq] at h₁ h₂
  exact ⟨⟨mt, hmt, List.length_eq_zero_iff.mp hlen⟩, ⟨f, hs ▸ hrun, hb'.1.1⟩,
    ⟨fs, fg, hs ▸ hfs, h₁.1, h₂.1, h₁.2.1, h₂.2.2⟩, ⟨g, hs ▸ hg, hgv⟩⟩

/-- `sgInst` is the instance of A's module. -/
theorem sg_isInst : setGetS.mod.IsInst sgInst := by
  obtain ⟨⟨mt, hmt, himp⟩, ⟨f, hf, hfa⟩, ⟨fs, fg, hfuncs, hts, htg, _, _⟩, _⟩ := sgFacts
  refine ⟨⟨mt, ⟨hmt, ?_, ?_, ?_, ?_⟩⟩, rfl, rfl⟩
  · intro xt hxt
    rw [himp] at hxt
    cases hxt
  · rw [himp]
    exact .nil
  · refine ⟨f, ?_, hfa⟩
    rw [himp]
    exact hf
  · refine .cons ⟨fs, ?_, hts⟩ (.cons ⟨fg, ?_, htg⟩ .nil)
    · show sgStore.funcs[0]? = some fs
      rw [hfuncs]
      rfl
    · show sgStore.funcs[1]? = some fg
      rw [hfuncs]
      rfl

theorem setGetS_good : setGetS.Good :=
  ⟨by decide, by
    intro x hx
    simp only [setGetS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨"set", rfl⟩
    · exact ⟨"get", rfl⟩⟩

/-- The store after `set`: the global holds `1`. -/
def sgStore₁ : Store Nat := sgStore.setGlobal 0 (Val.i32 1)

theorem sgStore₁_globals {g : GlobalInst} (hg : sgStore.globals = [g]) :
    sgStore₁.globals = [{ g with value := Val.i32 1 }] := by
  unfold sgStore₁ Store.setGlobal
  rw [hg]
  rfl

/-- **`set` writes the global and traps**, for every profile. -/
theorem set_run {P : Profile} :
    Steps P Det.noHost (invoke sgStore 0 []) ⟨sgStore₁, {}, [.trap]⟩ := by
  obtain ⟨_, _, ⟨fs, fg, hfuncs, hts, _, hset, _⟩, ⟨g, hglob, _⟩⟩ := sgFacts
  obtain ⟨code, x, hcode, hloc, hbody, hx, hmg⟩ := isSet_code hset
  have hf : sgStore.funcs[0]? = some fs := by rw [hfuncs]; rfl
  have he : Expand fs.type unitFn.toComp := FnType.expand_of_ofDefType? hts
  let F := Frame.forCall fs.module [] code.locals
  let n := (Ty.ofList (unitFn.results.map ScalarType.toC)).length
  have s₁ : Step P Det.noHost (invoke sgStore 0 [])
      ⟨sgStore, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf he (Ty.length_ofList (unitFn.params.map ScalarType.toC)).symm hcode
  have hg : sgStore.global? F x = some (0, g) := by
    show sgStore.global? (Frame.forCall fs.module [] code.locals) x = _
    simp [Store.global?, Frame.forCall, hmg, hx, hglob]
  have a₁ : Step P Det.noHost
      ⟨sgStore, F, vals [] ++ [(Val.i32 1).toAdmin, .plain (.globalSet x)] ++ [.plain .unreachable]⟩
      ⟨sgStore₁, F, vals [] ++ [] ++ [.plain .unreachable]⟩ :=
    .ctxtInstrs (.variable (.globalSet hg)) (.inr (by simp))
  have a₂ : Step P Det.noHost ⟨sgStore₁, F, [.plain .unreachable]⟩ ⟨sgStore₁, F, [.trap]⟩ :=
    .parametric .unreachable
  have s₂ : Steps P Det.noHost ⟨sgStore, F, expression code.body⟩ ⟨sgStore₁, F, [.trap]⟩ := by
    rw [hbody]
    exact (Relation.ReflTransGen.single a₁).tail a₂
  have s₃ := Litmus.steps_frame_label (f := {}) (n := n) (m := n) (cont := []) s₂
  exact (Relation.ReflTransGen.single s₁).trans ((s₃.tail (.ctxtFrame .trapLabel)).tail .trapFrame)

/-- **`get` returns the global**, from every store with A's functions and one global, for
every profile. -/
theorem get_run {P : Profile} {s : Store Nat} {g : GlobalInst} (hfs : s.funcs = sgStore.funcs)
    (hgs : s.globals = [g]) :
    Steps P Det.noHost (invoke s 1 []) ⟨s, {}, vals [g.value]⟩ := by
  obtain ⟨_, _, ⟨fs, fg, hfuncs, _, htg, _, hget⟩, _⟩ := sgFacts
  obtain ⟨code, x, hcode, hloc, hbody, hx, hmg⟩ := isGet_code hget
  have hf : s.funcs[1]? = some fg := by rw [hfs, hfuncs]; rfl
  have he : Expand fg.type i32Fn.toComp := FnType.expand_of_ofDefType? htg
  let F := Frame.forCall fg.module [] code.locals
  let n := (Ty.ofList (i32Fn.results.map ScalarType.toC)).length
  have hn : [g.value].length = n := (Ty.length_ofList (i32Fn.results.map ScalarType.toC)).symm
  have s₁ : Step P Det.noHost (invoke s 1 [])
      ⟨s, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf he (Ty.length_ofList (i32Fn.params.map ScalarType.toC)).symm hcode
  have hg : s.global? F x = some (0, g) := by
    show s.global? (Frame.forCall fg.module [] code.locals) x = _
    simp [Store.global?, Frame.forCall, hmg, hx, hgs]
  have s₂ : Steps P Det.noHost ⟨s, F, expression code.body⟩ ⟨s, F, vals [g.value]⟩ := by
    rw [hbody]
    exact .single (.variable (.globalGet hg))
  exact (Relation.ReflTransGen.single s₁).trans
    (((Litmus.steps_frame_label (f := {}) (n := n) (m := n) (cont := []) s₂).tail
      (.ctxtFrame .labelVals)).tail (.frameVals hn))

/-- **`set` is a trapped call of the specification**, leaving `sgStore₁`, for every profile. -/
theorem set_trapAt (P : Profile) :
    TrapAt P setGetS sgInst setGetS.exports[0] [] sgStore sgStore₁ := by
  have run : Steps P Det.noHost
      ((Thread.invokeFlat 0 (lowerArgs setGetS.exports[0].ty.params [])).config sgStore)
      ⟨sgStore₁, {}, [.trap]⟩ := set_run
  obtain ⟨s', t', hr, hd⟩ := Litmus.reach_of_steps run
  have hs : s' = sgStore₁ := by
    have h₁ : (t'.config s').store = s' := by cases t' <;> rfl
    rw [← h₁, hd]
  subst hs
  have hres : ResultAt sgStore₁ t' .trap := by
    show (t'.config sgStore₁).code = _
    rw [hd]
    rfl
  exact ⟨rfl, t', .trap, hr, hres, rfl⟩

/-- **`get` is a returned call of the specification** answering the global, for every
profile. -/
theorem get_retAt (P : Profile) {s : Store Nat} {g : GlobalInst} {v : BitVec 32}
    (hfs : s.funcs = sgStore.funcs) (hgs : s.globals = [g]) (hv : g.value = Val.i32 v) :
    RetAt P setGetS sgInst setGetS.exports[1] [] s [.u32 v] s := by
  have run : Steps P Det.noHost
      ((Thread.invokeFlat 1 (lowerArgs setGetS.exports[1].ty.params [])).config s)
      ⟨s, {}, vals [Val.i32 v]⟩ := by
    have h := get_run (P := P) hfs hgs
    rw [hv] at h
    exact h
  obtain ⟨s', t', hr, hd⟩ := Litmus.reach_of_steps run
  have hs : s' = s := by
    have h₁ : (t'.config s').store = s' := by cases t' <;> rfl
    rw [← h₁, hd]
  rw [hs] at hr hd
  have hres : ResultAt s t' (.values [Val.i32 v]) := by
    show (t'.config s).code = _
    rw [hd]
    rfl
  exact ⟨rfl, t', [Val.i32 v], [Flat.i32 v], hr, hres, rfl, rfl⟩

/-! ## The importer B -/

/-- The closed import types of `LinkedSession.pokePeekCore`. -/
def ppImports : List DefType :=
  match validate? LinkedSession.pokePeekCore with
  | some mt => CExternType.funcs mt.imports
  | none => []

/-- The store of the instance of `LinkedSession.pokePeekCore` against two host functions. -/
def ppStore : Store Nat :=
  match instantiateOnce? (importStore ppImports) LinkedSession.pokePeekCore [.func 0, .func 1] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `LinkedSession.pokePeekCore`. -/
def ppInst : ScalarInstance where
  imports := [unitFn, i32Fn]
  exports := [unitFn, i32Fn]
  addrs := [2, 3]
  store := ppStore

/-- The function instance is the host function `k`. -/
def isHost (k : Nat) (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .host h => h == k
  | _ => false

/-- The function instance has the body `call k`, no locals, and its module's function `k` is at
address `k`. -/
def isCallF (k : Nat) (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.call x]⟩ => x.toNat == k && fi.module.funcs[k]? == some k
  | _ => false

/-- What the summary records of a function instance of B. -/
def ppInfo (fi : FuncInst Nat) : Option FnType × Bool × Bool × Bool × Bool :=
  (FnType.ofDefType? fi.type, isHost 0 fi, isHost 1 fi, isCallF 0 fi, isCallF 1 fi)

/-- The checks on the instantiated store and frame. -/
def ppBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [2, 3] &&
    s.funcs.map ppInfo == [(some unitFn, true, false, false, false),
      (some i32Fn, false, true, false, false), (some unitFn, false, false, true, false),
      (some i32Fn, false, false, false, true)]

/-- The Boolean summary of the instantiation of `LinkedSession.pokePeekCore`. -/
def ppSummary : Bool :=
  match validate? LinkedSession.pokePeekCore with
  | some mt => mt.imports.length == 2 && mt.imports.all Litmus.isFuncImport &&
      (CExternType.funcs mt.imports).map FnType.ofDefType? == [some unitFn, some i32Fn] &&
      Litmus.runOk ppBody (instantiateOnce? (importStore (CExternType.funcs mt.imports))
        LinkedSession.pokePeekCore [.func 0, .func 1])
  | none => false

theorem ppSummary_eq : ppSummary = true := by decide +kernel

theorem isHost_code {k : Nat} {fi : FuncInst Nat} (h : isHost k fi = true) :
    fi.code = .host k := by
  unfold isHost at h
  split at h
  next h' hc => rw [hc, beq_iff_eq.mp h]
  next => cases h

theorem isCallF_code {k : Nat} {fi : FuncInst Nat} (h : isCallF k fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.FuncIdx), fi.code = .wasm code ∧
      code.locals = [] ∧ code.body = [.call x] ∧ x.toNat = k ∧ fi.module.funcs[k]? = some k := by
  unfold isCallF at h
  split at h
  next t x hc =>
    have h' : x.toNat = k ∧ fi.module.funcs[k]? = some k := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    exact ⟨_, x, hc, rfl, rfl, h'.1, h'.2⟩
  next => cases h

/-- The facts the summary records. -/
structure PpFacts : Prop where
  valid : ∃ mt, validate? LinkedSession.pokePeekCore = some mt ∧ mt.imports.length = 2 ∧
    (∀ xt ∈ mt.imports, ∃ d, xt = .func d) ∧
    List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft) (CExternType.funcs mt.imports)
      [unitFn, i32Fn] ∧
    ∃ f : Frame, instantiateOnce? (importStore (CExternType.funcs mt.imports))
      LinkedSession.pokePeekCore [.func 0, .func 1] = some (ppStore, f, none) ∧
      exportFuncAddrs f.module = [2, 3]
  funcs : ∃ h₀ h₁ fp fk : FuncInst Nat, ppStore.funcs = [h₀, h₁, fp, fk] ∧
    ppInfo h₀ = (some unitFn, true, false, false, false) ∧
    ppInfo h₁ = (some i32Fn, false, true, false, false) ∧
    ppInfo fp = (some unitFn, false, false, true, false) ∧
    ppInfo fk = (some i32Fn, false, false, false, true)

theorem ppFacts : PpFacts := by
  obtain ⟨mt, hmt⟩ : ∃ mt, validate? LinkedSession.pokePeekCore = some mt := by
    cases hv : validate? LinkedSession.pokePeekCore with
    | none => exact absurd ppSummary_eq (by simp [ppSummary, hv])
    | some mt => exact ⟨mt, rfl⟩
  have h' : ((mt.imports.length = 2 ∧ mt.imports.all Litmus.isFuncImport = true) ∧
      (CExternType.funcs mt.imports).map FnType.ofDefType? = [some unitFn, some i32Fn]) ∧
      Litmus.runOk ppBody (instantiateOnce? (importStore (CExternType.funcs mt.imports))
        LinkedSession.pokePeekCore [.func 0, .func 1]) = true := by
    simpa only [ppSummary, hmt, Bool.and_eq_true, beq_iff_eq] using ppSummary_eq
  obtain ⟨s, f, hrun, hb⟩ := Litmus.runOk_eq h'.2
  have himp : ppImports = CExternType.funcs mt.imports := by simp only [ppImports, hmt]
  have hs : ppStore = s := by simp only [ppStore, himp, hrun]
  have hb' : exportFuncAddrs f.module = [2, 3] ∧
      s.funcs.map ppInfo = [(some unitFn, true, false, false, false),
        (some i32Fn, false, true, false, false), (some unitFn, false, false, true, false),
        (some i32Fn, false, false, false, true)] := by
    simpa only [ppBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨d₀, d₁, hd, hd₀, hd₁⟩ := pair_of_map h'.1.2
  have hfun : ∀ xt ∈ mt.imports, ∃ d, xt = .func d := fun xt hxt =>
    Litmus.func_of_isFuncImport (List.all_eq_true.mp h'.1.1.2 xt hxt)
  obtain ⟨h₀, h₁, fp, fk, hfs, i₀, i₁, ip, ik⟩ := four_of_map hb'.2
  exact ⟨⟨mt, hmt, h'.1.1.1, hfun, hd ▸ .cons hd₀ (.cons hd₁ .nil), f, hs ▸ hrun, hb'.1⟩,
    ⟨h₀, h₁, fp, fk, hs ▸ hfs, i₀, i₁, ip, ik⟩⟩

/-- `ppInst` is the instance of B's module. -/
theorem pp_isInst : pokePeekI.mod.IsInst ppInst := by
  obtain ⟨⟨mt, hmt, hlen, hfun, hty, f, hf, hfa⟩, ⟨h₀, h₁, fp, fk, hfuncs, -, -, ip, ik⟩⟩ :=
    ppFacts
  simp only [ppInfo, Prod.mk.injEq] at ip ik
  have hr : (List.range mt.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func =
      [.func 0, .func 1] := by
    rw [hlen]
    rfl
  refine ⟨⟨mt, ⟨hmt, hfun, hty, ⟨f, ?_, hfa⟩, ?_⟩⟩, rfl, rfl⟩
  · rw [hr]
    exact hf
  · refine .cons ⟨fp, ?_, ip.1⟩ (.cons ⟨fk, ?_, ik.1⟩ .nil)
    · show ppStore.funcs[2]? = some fp
      rw [hfuncs]
      rfl
    · show ppStore.funcs[3]? = some fk
      rw [hfuncs]
      rfl

theorem pokePeekI_good : pokePeekI.Good :=
  ⟨by decide, by
    intro x hx
    simp only [pokePeekI, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨"poke", rfl⟩
    · exact ⟨"peek", rfl⟩, rfl⟩

/-! ## The importer's plays -/

/-- The callout context of an export call of B: its frame and its body's label. -/
def ppCtx (n : Nat) (F : Frame) : Ctx := .frame [] n F (.label [] n [] (.top [] []) []) []

/-- **An export call of B reaches its import call**: the function at `a` (body `call k`) calls
the host function `k` with no arguments, host-free, the store unchanged. -/
theorem pp_callout (P : Profile) {a k : Nat} {fi fh : FuncInst Nat} {ft fth : FnType}
    (hf : ppStore.funcs[a]? = some fi) (he : Expand fi.type ft.toComp) (hps : ft.params = [])
    (hc : isCallF k fi = true) (hfh : ppStore.funcs[k]? = some fh)
    (heh : Expand fh.type fth.toComp) (hph : fth.params = []) (hcode : fh.code = .host k) :
    ∃ (t : Thread) (F : Frame), Reach P (ppStore, .pending a []) (ppStore, t) ∧
      decompose? ppStore (t.config ppStore).code =
        some (ppCtx (Ty.ofList (ft.results.map ScalarType.toC)).length F, k, k, []) ∧
      (t.config ppStore).frame = {} := by
  obtain ⟨code, x, hcode', hloc, hbody, hx, hm⟩ := isCallF_code hc
  let F := Frame.forCall fi.module [] code.locals
  let n := (Ty.ofList (ft.results.map ScalarType.toC)).length
  have hn : ([] : List Silmaril.Wasm.Execution.Core.Val).length =
      (Ty.ofList (ft.params.map ScalarType.toC)).length := by
    rw [Ty.length_ofList, hps]
    rfl
  have s₁ : Step P Det.noHost (invoke ppStore a [])
      ⟨ppStore, {}, [.frame n F [.label n [] (expression code.body)]]⟩ :=
    .callRefFunc trivial hf he hn hcode'
  have hxF : F.module.funcs[x.toNat]? = some k := by rw [hx]; exact hm
  have s₂ : Steps P Det.noHost ⟨ppStore, F, expression code.body⟩
      ⟨ppStore, F, [.ref (.func k), .callRefType fh.type]⟩ := by
    rw [hbody]
    exact .single (.call hxF hfh)
  have run : Steps P Det.noHost ((Thread.pending a []).config ppStore)
      ⟨ppStore, {}, (ppCtx n F).fill (vals [] ++ [.ref (.func k), .callRefType fh.type])⟩ :=
    (Relation.ReflTransGen.single s₁).trans (Litmus.steps_frame_label s₂)
  obtain ⟨s₁', t₁, hr₁, hd₁⟩ := Litmus.reach_of_steps run
  have hs₁ : s₁' = ppStore := by
    have h₁ : (t₁.config s₁').store = s₁' := by cases t₁ <;> rfl
    rw [← h₁, hd₁]
  subst hs₁
  have hn' : ([] : List Silmaril.Wasm.Execution.Core.Val).length =
      (Ty.ofList (fth.params.map ScalarType.toC)).length := by
    rw [Ty.length_ofList, hph]
    rfl
  refine ⟨t₁, F, hr₁, ?_, by rw [hd₁]⟩
  rw [hd₁]
  exact Silmaril.Proofs.Wasm.Game.Linking.decompose?_fill _ trivial hfh heh hn' hcode

/-- The export question `poke()`. -/
def pokeQ : ppInst.F.Op := ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩

/-- The export question `peek()`. -/
def peekQ : ppInst.F.Op := ⟨⟨1, by decide⟩, ⟨[], .nil⟩⟩

/-- The import question `set()`. -/
def setE : ppInst.E.Op := ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩

/-- The import question `get()`. -/
def getE : ppInst.E.Op := ⟨⟨1, by decide⟩, ⟨[], .nil⟩⟩

/-- The answer `y` of the import question `get()`. -/
def getAI (y : BitVec 32) : ppInst.E.Ar getE := .values ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩

/-- The answer `y` of the export question `peek()`. -/
def peekAO (y : BitVec 32) : ppInst.F.Ar peekQ := .values ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩

theorem set_importOp : ppInst.importOp? 0 [] = some setE := by
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · split
    · rfl
    · exact absurd setE.2.2 ‹_›
  · exact absurd (show 0 < ppInst.imports.length by decide) ‹_›

theorem get_importOp : ppInst.importOp? 1 [] = some getE := by
  unfold ScalarInstance.importOp? ifaceOp?
  split
  · split
    · rfl
    · exact absurd getE.2.2 ‹_›
  · exact absurd (show 1 < ppInst.imports.length by decide) ‹_›

/-- **`poke` with its import call `set` answered by a trap** answers a trap, for every
profile. -/
theorem poke_path (P : Profile) :
    ppInst.Path P (.idle ppInst.store)
      ([.inr (.ask pokeQ)] ++ [.inl (.ask setE), .inl (.ans setE .trap), .inr (.ans pokeQ .trap)])
      (.idle ppStore) := by
  obtain ⟨_, ⟨h₀, h₁, fp, fk, hfuncs, i₀, _, ip, _⟩⟩ := ppFacts
  simp only [ppInfo, Prod.mk.injEq] at i₀ ip
  have hf2 : ppStore.funcs[2]? = some fp := by rw [hfuncs]; rfl
  have hf0 : ppStore.funcs[0]? = some h₀ := by rw [hfuncs]; rfl
  obtain ⟨t, F, hr, hd, -⟩ := pp_callout P hf2 (FnType.expand_of_ofDefType? ip.1) rfl
    ip.2.2.2.1 hf0 (FnType.expand_of_ofDefType? i₀.1) rfl (isHost_code i₀.2.1)
  exact trapImport_path (.cons (.call _ _) (.nil _)) hr ⟨_, _, hd⟩ set_importOp

/-- **`peek` with its import call `get` answered `y`** answers `y`, for every profile. -/
theorem peek_path (P : Profile) (y : BitVec 32) :
    ppInst.Path P (.idle ppStore)
      (.inr (.ask peekQ) :: callMoves [⟨getE, getAI y⟩] ++ [.inr (.ans peekQ (peekAO y))])
      (.idle ppStore) := by
  obtain ⟨_, ⟨h₀, h₁, fp, fk, hfuncs, _, i₁, _, ik⟩⟩ := ppFacts
  simp only [ppInfo, Prod.mk.injEq] at i₁ ik
  have hf3 : ppStore.funcs[3]? = some fk := by rw [hfuncs]; rfl
  have hf1 : ppStore.funcs[1]? = some h₁ := by rw [hfuncs]; rfl
  obtain ⟨t, F, hr, hd, hfr⟩ := pp_callout P hf3 (FnType.expand_of_ofDefType? ik.1) rfl
    ik.2.2.2.2 hf1 (FnType.expand_of_ofDefType? i₁.1) rfl (isHost_code i₁.2.2.1)
  let n := (Ty.ofList (i32Fn.results.map ScalarType.toC)).length
  have hn : [Val.i32 y].length = n := (Ty.length_ofList (i32Fn.results.map ScalarType.toC)).symm
  have hres : resumeResult ppStore t (Answer.toResult (getAI y)) =
      .active {} [.frame n F [.label n [] (vals [Val.i32 y])]] := by
    unfold resumeResult
    simp only [hd, hfr]
    rfl
  have run₂ : Steps P Det.noHost
      ((Thread.active {} [.frame n F [.label n [] (vals [Val.i32 y])]]).config ppStore)
      ⟨ppStore, {}, vals [Val.i32 y]⟩ :=
    (Relation.ReflTransGen.single (.ctxtFrame .labelVals)).tail (.frameVals hn)
  obtain ⟨s₂', t₂, hr₂, hd₂⟩ := Litmus.reach_of_steps run₂
  have hs₂ : s₂' = ppStore := by
    have h₂ : (t₂.config s₂').store = s₂' := by cases t₂ <;> rfl
    rw [← h₂, hd₂]
  subst hs₂
  have hfin : ResultAt ppStore t₂ (.values [Val.i32 y]) := by
    show (t₂.config ppStore).code = _
    rw [hd₂]
    rfl
  have hans : Answer.ofResult? (ppInst.exports.get peekQ.1) (.values [Val.i32 y]) =
      some (peekAO y) := by
    unfold Answer.ofResult?
    exact dite_eq_left (.cons ⟨y, rfl⟩ .nil)
  refine .cons (.call _ _) (.cons (.ucall hr ⟨_, _, hd⟩ get_importOp)
    (.cons (.uret (getAI y)) ?_))
  rw [hres]
  exact .cons (.oret hr₂ hfin hans) (.nil _)

theorem set_impRel :
    Silmaril.Wasm.Component.Reference.ImpRel pokePeekI ppInst ⟨setE, .trap⟩
      [⟨(⟨0, by decide⟩, .vals []), none⟩] :=
  impRel_trap (e := setE) (nm := "set") (ft := unitTy) rfl rfl

theorem get_impRel (y : BitVec 32) :
    Silmaril.Wasm.Component.Reference.ImpRel pokePeekI ppInst ⟨getE, getAI y⟩
      [⟨(⟨1, by decide⟩, .vals []), some (.vals [.u32 y])⟩] := by
  refine ⟨"get", u32Ty, some (.flat [Flat.i32 y]), rfl, ?_, ?_⟩
  · show payloadAnswer (ppInst.imports.get getE.1) (some (.flat [Flat.i32 y])) = getAI y
    have ht : typed? (ppInst.imports.get getE.1).results ([Flat.i32 y].map ofFlat) =
        some ⟨[Val.i32 y], .cons ⟨y, rfl⟩ .nil⟩ := by
      unfold typed?
      exact dite_eq_left (.cons ⟨y, rfl⟩ .nil)
    unfold payloadAnswer
    dsimp only
    erw [ht]
    rfl
  · exact ⟨show 1 < 2 by decide, _, rfl, rfl⟩

/-! ## The linked plays -/

/-- The session round `poke()`: its import call `set` traps. -/
def pokeR : Linked2.SessRound linkedC ppInst where
  j := ⟨0, by decide⟩
  vs := []
  f := pokeQ
  cs := [⟨setE, .trap⟩]
  w := .trap
  dss := [[⟨(⟨0, by decide⟩, .vals []), none⟩]]

/-- The session round `peek()`: its import call `get` answers `y`. -/
def peekR (y : BitVec 32) : Linked2.SessRound linkedC ppInst where
  j := ⟨1, by decide⟩
  vs := []
  f := peekQ
  cs := [⟨getE, getAI y⟩]
  w := peekAO y
  dss := [[⟨(⟨1, by decide⟩, .vals []), some (.vals [.u32 y])⟩]]

theorem pokeR_ok : pokeR.Ok := ⟨[], rfl, rfl, rfl, .cons set_impRel .nil⟩

theorem peekR_ok (y : BitVec 32) : (peekR y).Ok := ⟨[], rfl, rfl, rfl, .cons (get_impRel y) .nil⟩

/-- **The linked IR persists the callee-trap store**: for every profile, `poke` answers a trap
(A's `set` writes the global and traps inside B's import call) and the following `peek` answers
`1` (A's `get`, from the store `set`'s trap left). -/
theorem linkedC_ir_session (P : Profile) :
    ([.inr (.ask (⟨0, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨0, by decide⟩, .vals [])) none),
      .inr (.ask (⟨1, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨1, by decide⟩, .vals [])) (some (.vals [.u32 1])))] :
      List (Move (linkedC.toComp.imports.sig) (sigN linkedC.toComp.exports.length))) ∈
      linkedC.toComp.den (impSem P) := by
  obtain ⟨_, _, _, ⟨g, hglob, _⟩⟩ := sgFacts
  have hpath : ppInst.Path P (.idle ppInst.store)
      ([pokeR, peekR 1].flatMap Linked2.SessRound.instMoves) (.idle ppStore) :=
    path_append (poke_path P) (peek_path P 1)
  have hrun : Linked2.ExpRunT P linkedC sgInst sgInst.store
      ([⟨(⟨0, by decide⟩, .vals []), none⟩, ⟨(⟨1, by decide⟩, .vals []), some (.vals [.u32 1])⟩] :
        List (Round (sigN linkedC.imp.imports.length))) sgStore₁ :=
    .trap ⟨0, by decide⟩ rfl (set_trapAt P)
      (.ret ⟨1, by decide⟩ rfl (get_retAt P rfl (sgStore₁_globals hglob) rfl) (.nil _))
  have hok : ∀ d ∈ [pokeR, peekR 1], d.Ok := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact pokeR_ok
    · exact peekR_ok 1
  exact linked2_sessToIR P linkedC setGetS_good pokePeekI_good sgInst sg_isInst ppInst pp_isInst
    [pokeR, peekR 1] hok _ hpath _ hrun

/-- **`peek` on a fresh instance answers `0`**, for every profile. -/
theorem linkedC_ir_peek_fresh (P : Profile) :
    ([.inr (.ask (⟨1, by decide⟩, .vals [])),
      .inr (.ans (m := (⟨1, by decide⟩, .vals [])) (some (.vals [.u32 0])))] :
      List (Move (linkedC.toComp.imports.sig) (sigN linkedC.toComp.exports.length))) ∈
      linkedC.toComp.den (impSem P) := by
  obtain ⟨_, _, _, ⟨g, hglob, hg0⟩⟩ := sgFacts
  have hpath : ppInst.Path P (.idle ppInst.store)
      ([peekR 0].flatMap Linked2.SessRound.instMoves) (.idle ppStore) :=
    peek_path P 0
  have hrun : Linked2.ExpRunT P linkedC sgInst sgInst.store
      ([⟨(⟨1, by decide⟩, .vals []), some (.vals [.u32 0])⟩] :
        List (Round (sigN linkedC.imp.imports.length))) sgStore :=
    .ret ⟨1, by decide⟩ rfl (get_retAt P rfl hglob hg0) (.nil _)
  have hok : ∀ d ∈ [peekR 0], d.Ok := by
    intro d hd
    rw [List.mem_singleton] at hd
    subst hd
    exact peekR_ok 0
  exact linked2_sessToIR P linkedC setGetS_good pokePeekI_good sgInst sg_isInst ppInst pp_isInst
    [peekR 0] hok _ hpath _ hrun

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR
