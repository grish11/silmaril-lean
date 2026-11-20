module

public import Silmaril.Wasm.Component.Reference.HAcceptTuple.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.Fixture

/-!
# The `tuple<u8, u8>` acceptor: the instance and the adequacy hypotheses

* `tcFacts`, `tc_isInst`: the instance of `tupleCore` against one host function (kernel
  evaluation of a Boolean summary of validation and instantiation).
* `tupleL_adequate : tupleL.Adequate`, `tupleL_hostTyped : tupleL.HostTyped acceptG`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference.HAcceptTuple
open Silmaril.Wasm.Component.Reference.LinkedSession (setGetCore setGetS unitTy unitFlat)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionIR
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- The scalar type `[i32, i32] -> []`. -/
abbrev pairFn : FnType := ⟨[.num (.int .i32), .num (.int .i32)], []⟩

/-- The closed import types of `tupleCore`. -/
def tcImports : List DefType :=
  match validate? tupleCore with
  | some mt => CExternType.funcs mt.imports
  | none => []

/-- The store of the instance of `tupleCore` against one host function. -/
def tcStore : Store Nat :=
  match instantiateOnce? (importStore tcImports) tupleCore [.func 0] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `tupleCore`. -/
def tcInst : ScalarInstance where
  imports := [pairFn]
  exports := [unitFn]
  addrs := [1]
  store := tcStore

/-- The function instance has the body `i32.const 104; i32.const 105; call k`, no locals, and
its module's function `k` is at address `k`. -/
def isRun (k : Nat) (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.intConst .i32 a, .intConst .i32 b, .call x]⟩ =>
    a == 104 && b == 105 && x.toNat == k && fi.module.funcs[k]? == some k
  | _ => false

/-- What the summary records of a function instance. -/
def tcInfo (fi : FuncInst Nat) : Option FnType × Bool × Bool :=
  (FnType.ofDefType? fi.type, isHost 0 fi, isRun 0 fi)

/-- The checks on the instantiated store and frame. -/
def tcBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [1] &&
    s.funcs.map tcInfo == [(some pairFn, true, false), (some unitFn, false, true)]

/-- The Boolean summary of the instantiation of `tupleCore`. -/
def tcSummary : Bool :=
  match validate? tupleCore with
  | some mt => mt.imports.length == 1 && mt.imports.all Litmus.isFuncImport &&
      (CExternType.funcs mt.imports).map FnType.ofDefType? == [some pairFn] &&
      Litmus.runOk tcBody (instantiateOnce? (importStore (CExternType.funcs mt.imports))
        tupleCore [.func 0])
  | none => false

theorem tcSummary_eq : tcSummary = true := by decide +kernel

theorem isRun_code {k : Nat} {fi : FuncInst Nat} (h : isRun k fi = true) :
    ∃ (code : Silmaril.Wasm.Func) (x : Silmaril.Wasm.FuncIdx), fi.code = .wasm code ∧
      code.locals = [] ∧
      code.body = [.intConst .i32 104, .intConst .i32 105, .call x] ∧ x.toNat = k ∧
      fi.module.funcs[k]? = some k := by
  unfold isRun at h
  split at h
  next t a b x hc =>
    have h' : ((a = 104 ∧ b = 105) ∧ x.toNat = k) ∧ fi.module.funcs[k]? = some k := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    obtain ⟨⟨⟨rfl, rfl⟩, hx⟩, hm⟩ := h'
    exact ⟨_, x, hc, rfl, rfl, hx, hm⟩
  next => cases h

/-- The facts the summary records. -/
structure TcFacts : Prop where
  valid : ∃ mt, validate? tupleCore = some mt ∧ mt.imports.length = 1 ∧
    (∀ xt ∈ mt.imports, ∃ d, xt = .func d) ∧
    List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft) (CExternType.funcs mt.imports)
      [pairFn] ∧
    ∃ f : Frame, instantiateOnce? (importStore (CExternType.funcs mt.imports))
      tupleCore [.func 0] = some (tcStore, f, none) ∧ exportFuncAddrs f.module = [1]
  funcs : ∃ h₀ fr : FuncInst Nat, tcStore.funcs = [h₀, fr] ∧
    tcInfo h₀ = (some pairFn, true, false) ∧ tcInfo fr = (some unitFn, false, true)

theorem tcFacts : TcFacts := by
  obtain ⟨mt, hmt⟩ : ∃ mt, validate? tupleCore = some mt := by
    cases hv : validate? tupleCore with
    | none => exact absurd tcSummary_eq (by simp [tcSummary, hv])
    | some mt => exact ⟨mt, rfl⟩
  have h' : ((mt.imports.length = 1 ∧ mt.imports.all Litmus.isFuncImport = true) ∧
      (CExternType.funcs mt.imports).map FnType.ofDefType? = [some pairFn]) ∧
      Litmus.runOk tcBody (instantiateOnce? (importStore (CExternType.funcs mt.imports))
        tupleCore [.func 0]) = true := by
    simpa only [tcSummary, hmt, Bool.and_eq_true, beq_iff_eq] using tcSummary_eq
  obtain ⟨s, f, hrun, hb⟩ := Litmus.runOk_eq h'.2
  have himp : tcImports = CExternType.funcs mt.imports := by simp only [tcImports, hmt]
  have hs : tcStore = s := by simp only [tcStore, himp, hrun]
  have hb' : exportFuncAddrs f.module = [1] ∧
      s.funcs.map tcInfo = [(some pairFn, true, false), (some unitFn, false, true)] := by
    simpa only [tcBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨d₀, hd, hd₀⟩ := single_of_map h'.1.2
  have hfun : ∀ xt ∈ mt.imports, ∃ d, xt = .func d := fun xt hxt =>
    Litmus.func_of_isFuncImport (List.all_eq_true.mp h'.1.1.2 xt hxt)
  obtain ⟨h₀, fr, hfs, i₀, ir⟩ := pair_of_map hb'.2
  exact ⟨⟨mt, hmt, h'.1.1.1, hfun, hd ▸ .cons hd₀ .nil, f, hs ▸ hrun, hb'.1⟩,
    ⟨h₀, fr, hs ▸ hfs, i₀, ir⟩⟩

/-- `tcInst` is the instance of `tupleCore`. -/
theorem tc_isInst : tupleI.mod.IsInst tcInst := by
  obtain ⟨⟨mt, hmt, hlen, hfun, hty, f, hf, hfa⟩, ⟨h₀, fr, hfuncs, -, ir⟩⟩ := tcFacts
  simp only [tcInfo, Prod.mk.injEq] at ir
  have hr : (List.range mt.imports.length).map Silmaril.Wasm.Execution.Core.ExternAddr.func =
      [.func 0] := by
    rw [hlen]
    rfl
  refine ⟨⟨mt, ⟨hmt, hfun, hty, ⟨f, ?_, hfa⟩, ?_⟩⟩, rfl, rfl⟩
  · rw [hr]
    exact hf
  · refine .cons ⟨fr, ?_, ir.1⟩ .nil
    show tcStore.funcs[1]? = some fr
    rw [hfuncs]
    rfl

theorem tupleI_good : tupleI.Good :=
  ⟨by decide, by
    intro x hx
    simp only [tupleI, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact ⟨"run", rfl⟩, rfl⟩

/-- The validated import types of `tupleCore`, summarised. -/
def tcImportsSummary : Bool :=
  match validate? tupleCore with
  | some mt => decide (mt.imports = tupleI.imports.map fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩))
  | none => false

theorem tcImportsSummary_eq : tcImportsSummary = true := by decide +kernel

theorem tc_importTypes : ∃ mt, validate? tupleI.mod.mod = some mt ∧
    mt.imports = tupleI.imports.map fun p =>
      .func (Silmaril.Wasm.SingleThreaded.ofFlatType ⟨p.2.flat.params, p.2.flat.results⟩) := by
  have h : tcImportsSummary = true := tcImportsSummary_eq
  unfold tcImportsSummary at h
  split at h
  next mt hmt => exact ⟨mt, hmt, of_decide_eq_true h⟩
  next => cases h

theorem tupleI_inst : tupleI.Inst :=
  ⟨⟨tcInst, tc_isInst⟩, by decide, by decide, rfl, tc_importTypes⟩

theorem tupleI_arity : tupleI.Arity := by
  unfold SimpleI.Arity
  decide

theorem tupleI_floatFree : tupleI.FloatFree := by
  unfold SimpleI.FloatFree
  decide

theorem tupleL_wireTy : tupleL.WireTy :=
  ⟨⟨rfl, by decide⟩, fun k w hk => by simp [tupleL] at hk⟩

theorem tupleL_namesOk : tupleL.toL2.NamesOk := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [tupleL, setGetS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ne_tag_of_length 2 (by decide) (by decide)
    · exact ne_tag_of_length 2 (by decide) (by decide)
  · simp only [tupleL, tupleI, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact ne_tag_of_length 2 (by decide) (by decide)

theorem tupleL_splitOk : tupleL.toL2.SplitOk :=
  ⟨⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **`tupleL` satisfies the adequacy hypotheses of `HLinkedSession`.** -/
theorem tupleL_adequate : tupleL.Adequate :=
  ⟨setGetS_good, setGetS_inst, tupleI_good, tupleI_inst, tupleI_arity, tupleI_floatFree,
    tupleL_wireTy, tupleL_namesOk, List.nodup_nil, tupleL_splitOk⟩

/-- **`acceptG` is a typed host for `tupleL`**: its answer `[]` is the image of the (empty)
results of `accept`. -/
theorem tupleL_hostTyped : tupleL.HostTyped acceptG := by
  intro s i hi ws rs s' h
  simp only [acceptG, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hi0 : i = 0 := by simpa [tupleL] using hi
  subst hi0
  exact ⟨[], rfl, rfl⟩

end Silmaril.Proofs.Wasm.Component.Reference.HAcceptTuple
