module

public import Silmaril.Wasm.Component.Reference.Adequacy.Defs
public import Silmaril.Proofs.Wasm.Component.Reference.Litmus

/-!
# The trap witnesses: instances and core runs

The instances of `pokePeekCore` and `zeroCore` are computed by kernel evaluation of
`validate?` and `instantiateOnce?` (`decide +kernel` on Boolean summaries, as for the litmus
components). The export calls are Core 3.0 runs built from `Step` rules, for every profile:

* `set_run`: `i32.const 1; global.set 0; i32.const 0` from the instance's store returns `0`
  and leaves the global at `1`;
* `get_run`: `global.get 0` returns the global, at every store with the instance's functions;
* `zero_run`: `i32.const 0` returns `0`, at every store with the instance's functions.

The runs are host-free thread runs (`Reach`) to a result, from which they follow for the
machine (`reach_of_steps`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Game
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Proofs.Wasm.Component.Reference.Litmus (runOk runOk_eq steps_frame_label)

/-- The function type `[] → [i32]`. -/
abbrev fnI32 : FnType := ⟨[], [.num (.int .i32)]⟩

/-! ## The instances -/

/-- The store of the instance of `pokePeekCore`. -/
def ppStore : Store Nat :=
  match instantiateOnce? (importStore []) pokePeekCore [] with
  | some (s, _, _) => s
  | none => {}

/-- The store of the instance of `zeroCore`. -/
def zStore : Store Nat :=
  match instantiateOnce? (importStore []) zeroCore [] with
  | some (s, _, _) => s
  | none => {}

/-- The instance of `pokePeekCore`. -/
def ppInst : ScalarInstance where
  imports := []
  exports := [fnI32, fnI32]
  addrs := [0, 1]
  store := ppStore

/-- The instance of `zeroCore`. -/
def zInst : ScalarInstance where
  imports := []
  exports := [fnI32]
  addrs := [0]
  store := zStore

/-- The body `i32.const 1; global.set 0; i32.const 0`. -/
def isSet (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.intConst .i32 a, .globalSet x, .intConst .i32 b]⟩ =>
    a == 1 && x.toNat == 0 && b == 0
  | _ => false

/-- The body `global.get 0`. -/
def isGet (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.globalGet x]⟩ => x.toNat == 0
  | _ => false

/-- The body `i32.const 0`. -/
def isZero (fi : FuncInst Nat) : Bool :=
  match fi.code with
  | .wasm ⟨_, [], [.intConst .i32 a]⟩ => a == 0
  | _ => false

/-- The checks on the store and frame of `pokePeekCore`. -/
def ppBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [0, 1] &&
    (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) == [some fnI32, some fnI32] &&
    (s.funcs.map isSet) == [true, false] && (s.funcs.map isGet) == [false, true] &&
    (s.funcs.map fun (fi : FuncInst Nat) => fi.module.globals) == [[0], [0]] &&
    (s.globals.map (·.value)) == [Val.i32 0]

/-- The checks on the store and frame of `zeroCore`. -/
def zBody (s : Store Nat) (f : Frame) : Bool :=
  exportFuncAddrs f.module == [0] &&
    (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) == [some fnI32] &&
    (s.funcs.map isZero) == [true]

/-- The Boolean summary of the instantiation of `pokePeekCore`. -/
def ppSummary : Bool :=
  ((validate? pokePeekCore).map (·.imports.length) == some 0) &&
    runOk ppBody (instantiateOnce? (importStore []) pokePeekCore [])

/-- The Boolean summary of the instantiation of `zeroCore`. -/
def zSummary : Bool :=
  ((validate? zeroCore).map (·.imports.length) == some 0) &&
    runOk zBody (instantiateOnce? (importStore []) zeroCore [])

theorem ppSummary_eq : ppSummary = true := by decide +kernel
theorem zSummary_eq : zSummary = true := by decide +kernel

/-- What the summary of `pokePeekCore` records. -/
structure PPFacts : Prop where
  valid : ∃ mt, validate? pokePeekCore = some mt ∧ mt.imports = []
  inst : ∃ f : Frame, instantiateOnce? (importStore []) pokePeekCore [] = some (ppStore, f, none) ∧
    exportFuncAddrs f.module = [0, 1]
  funcs : ∃ fi₀ fi₁ : FuncInst Nat, ppStore.funcs = [fi₀, fi₁] ∧
    FnType.ofDefType? fi₀.type = some fnI32 ∧ FnType.ofDefType? fi₁.type = some fnI32 ∧
    isSet fi₀ = true ∧ isGet fi₁ = true ∧ fi₀.module.globals = [0] ∧ fi₁.module.globals = [0]
  globals : ∃ g : GlobalInst, ppStore.globals = [g] ∧ g.value = Val.i32 0

/-- What the summary of `zeroCore` records. -/
structure ZFacts : Prop where
  valid : ∃ mt, validate? zeroCore = some mt ∧ mt.imports = []
  inst : ∃ f : Frame, instantiateOnce? (importStore []) zeroCore [] = some (zStore, f, none) ∧
    exportFuncAddrs f.module = [0]
  funcs : ∃ fi : FuncInst Nat, zStore.funcs = [fi] ∧ FnType.ofDefType? fi.type = some fnI32 ∧
    isZero fi = true

theorem ppFacts : PPFacts := by
  have h' : (validate? pokePeekCore).map (·.imports.length) = some 0 ∧
      runOk ppBody (instantiateOnce? (importStore []) pokePeekCore []) = true := by
    simpa only [ppSummary, Bool.and_eq_true, beq_iff_eq] using ppSummary_eq
  obtain ⟨mt, hmt, hlen⟩ := Option.map_eq_some_iff.mp h'.1
  obtain ⟨s, f, hrun, hb⟩ := runOk_eq h'.2
  have hs : ppStore = s := by simp only [ppStore, hrun]
  have hb' : (((((exportFuncAddrs f.module = [0, 1] ∧
      (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) =
        [some fnI32, some fnI32]) ∧ s.funcs.map isSet = [true, false]) ∧
      s.funcs.map isGet = [false, true]) ∧
      (s.funcs.map fun (fi : FuncInst Nat) => fi.module.globals) = [[0], [0]]) ∧
      s.globals.map (·.value) = [Val.i32 0]) := by
    simpa only [ppBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨⟨⟨⟨⟨hfa, hty⟩, hset⟩, hget⟩, hglob⟩, hval⟩ := hb'
  obtain ⟨fi₀, fi₁, hfi⟩ : ∃ fi₀ fi₁, s.funcs = [fi₀, fi₁] := by
    have hl : s.funcs.length = 2 := by simpa using congrArg List.length hty
    match hf : s.funcs, hl with
    | [fi₀, fi₁], _ => exact ⟨fi₀, fi₁, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, s.globals = [g] := by
    have hl : s.globals.length = 1 := by simpa using congrArg List.length hval
    match hf : s.globals, hl with
    | [g], _ => exact ⟨g, rfl⟩
  rw [hfi] at hty hset hget hglob
  rw [hg] at hval
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty hset hget hglob hval
  exact ⟨⟨mt, hmt, List.length_eq_zero_iff.mp hlen⟩, ⟨f, hs ▸ hrun, hfa⟩,
    ⟨fi₀, fi₁, hs ▸ hfi, hty.1, hty.2, hset.1, hget.2, hglob.1, hglob.2⟩, ⟨g, hs ▸ hg, hval⟩⟩

theorem zFacts : ZFacts := by
  have h' : (validate? zeroCore).map (·.imports.length) = some 0 ∧
      runOk zBody (instantiateOnce? (importStore []) zeroCore []) = true := by
    simpa only [zSummary, Bool.and_eq_true, beq_iff_eq] using zSummary_eq
  obtain ⟨mt, hmt, hlen⟩ := Option.map_eq_some_iff.mp h'.1
  obtain ⟨s, f, hrun, hb⟩ := runOk_eq h'.2
  have hs : zStore = s := by simp only [zStore, hrun]
  have hb' : (exportFuncAddrs f.module = [0] ∧
      (s.funcs.map fun (fi : FuncInst Nat) => FnType.ofDefType? fi.type) = [some fnI32]) ∧
      s.funcs.map isZero = [true] := by
    simpa only [zBody, Bool.and_eq_true, beq_iff_eq] using hb
  obtain ⟨⟨hfa, hty⟩, hz⟩ := hb'
  obtain ⟨fi, hfi⟩ : ∃ fi, s.funcs = [fi] :=
    List.length_eq_one_iff.mp (by simpa using congrArg List.length hty)
  rw [hfi] at hty hz
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hty hz
  exact ⟨⟨mt, hmt, List.length_eq_zero_iff.mp hlen⟩, ⟨f, hs ▸ hrun, hfa⟩, ⟨fi, hs ▸ hfi, hty, hz⟩⟩

/-- `ppInst` is the instance of the module of `pokePeekS`. -/
theorem pp_isInst : pokePeekS.mod.IsInst ppInst := by
  obtain ⟨⟨mt, hmt, himp⟩, ⟨f, hf, hfa⟩, ⟨fi₀, fi₁, hfuncs, hty₀, hty₁, -⟩, -⟩ := ppFacts
  refine ⟨⟨mt, ⟨hmt, ?_, ?_, ?_, ?_⟩⟩, rfl, rfl⟩
  · intro xt hxt
    rw [himp] at hxt
    cases hxt
  · rw [himp]
    exact .nil
  · refine ⟨f, ?_, hfa⟩
    rw [himp]
    exact hf
  · refine .cons ⟨fi₀, ?_, hty₀⟩ (.cons ⟨fi₁, ?_, hty₁⟩ .nil)
    · show ppStore.funcs[0]? = some fi₀
      rw [hfuncs]
      rfl
    · show ppStore.funcs[1]? = some fi₁
      rw [hfuncs]
      rfl

/-- `zInst` is the instance of the module of `zeroS`. -/
theorem z_isInst : zeroS.mod.IsInst zInst := by
  obtain ⟨⟨mt, hmt, himp⟩, ⟨f, hf, hfa⟩, ⟨fi, hfuncs, hty, -⟩⟩ := zFacts
  refine ⟨⟨mt, ⟨hmt, ?_, ?_, ?_, ?_⟩⟩, rfl, rfl⟩
  · intro xt hxt
    rw [himp] at hxt
    cases hxt
  · rw [himp]
    exact .nil
  · refine ⟨f, ?_, hfa⟩
    rw [himp]
    exact hf
  · refine .cons ⟨fi, ?_, hty⟩ .nil
    show zStore.funcs[0]? = some fi
    rw [hfuncs]
    rfl

theorem pokePeekS_adequate : pokePeekS.Adequate where
  good := ⟨by decide, by
    intro x hx
    simp only [pokePeekS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨"set", rfl⟩
    · exact ⟨"get", rfl⟩⟩
  floatFree := by
    intro x hx
    simp only [pokePeekS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact ⟨rfl, rfl⟩
  inst := ⟨⟨ppInst, pp_isInst⟩, rfl⟩
  arity := by
    intro x hx
    simp only [pokePeekS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

theorem zeroS_adequate : zeroS.Adequate where
  good := ⟨by decide, by
    intro x hx
    simp only [zeroS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact ⟨"f", rfl⟩⟩
  floatFree := by
    intro x hx
    simp only [zeroS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact ⟨rfl, rfl⟩
  inst := ⟨⟨zInst, z_isInst⟩, rfl⟩
  arity := by
    intro x hx
    simp only [zeroS, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
