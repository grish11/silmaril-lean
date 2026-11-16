module

public import Silmaril.Wasm.Abstract.FunctorP.Thms
public import Silmaril.Wasm.Abstract.PubViewExample.Defs

/-!
# Public does not imply open: proofs

* `reach_call`: in a one-function witness store whose frame names that function at index `1`,
  `[call 1]` has a pending call at the empty log, under every oracle.
* `not_reach_const`: `[i32.const 42]` has no pending call at any log (induction on `ReachXP`).
* `callStore_body`, `inlineStore_body`: function `0` of `callStore` (of `inlineStore`) is Wasm
  code whose lifted body is `[call 1]` (`[i32.const 42]`), by kernel evaluation of a Boolean
  check.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.PubOpenWitness

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.FunctorP
open Silmaril.Wasm.Abstract.PubViewExample

variable {H : Type}

/-! ## A pending call of `[call 1]` -/

/-- `(func)`: the defined type of a function with no parameters and no results. -/
def wType : Validation.DefType :=
  .defn (.group (.cons (.sub true .nil (.func .nil .nil)) .nil)) 0

theorem wType_funcType : Validation.DefType.funcType? wType = some ([], []) := by
  decide +kernel

/-- A function of type `wType` with an empty body. -/
def wFunc : FuncInst H := ⟨wType, {}, .wasm ⟨⟨0⟩, [], []⟩⟩

/-- A store with the one function `wFunc`, at address `0`. -/
def wStore : Store H := { funcs := [wFunc] }

/-- A frame whose module names the address `0` at function indices `0` and `1`. -/
def wFrame : Frame := { module := { funcs := [0, 0] } }

/-- **`[call 1]` has a pending call at the empty log**, under every oracle. -/
theorem reach_call (C : CallRel H) :
    ∃ y, ReachXP C (wStore (H := H)) wFrame [] [.op (.call ⟨1⟩) []] [] y :=
  ⟨_, .call .nil (.call (a := 0) (fi := wFunc) (ps := []) (rs := []) rfl wType_funcType)⟩

theorem not_reach_aux {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {cs : List (ACall H)} {y : Nat × List Val × Store H}
    (h : ReachXP C s f stk es cs y) :
    es = [] ∨ es = [.op (.intConst .i32 42) []] → False := by
  induction h with
  | head _ ih =>
    rintro (h | h)
    · cases h
    · obtain ⟨rfl, -⟩ := List.cons.inj h
      exact ih (.inr rfl)
  | cons _ _ ih₂ =>
    rintro (h | h)
    · cases h
    · obtain ⟨-, rfl⟩ := List.cons.inj h
      exact ih₂ (.inl rfl)
  | args _ ih =>
    rintro (h | h)
    · cases h
    · obtain ⟨h₁, -⟩ := List.cons.inj h
      cases h₁
      exact ih (.inl rfl)
  | call _ hy =>
    rintro (h | h)
    · cases h
    · obtain ⟨h₁, -⟩ := List.cons.inj h
      cases h₁
      cases hy
  | block | loop | loopBack | cond | arm | tryT =>
    rintro (h | h) <;> cases h

/-- **`[i32.const 42]` has no pending call**, at any oracle, store, frame, stack and log. -/
theorem not_reach_const {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {cs : List (ACall H)} {y : Nat × List Val × Store H} :
    ¬ ReachXP C s f stk [.op (.intConst .i32 42) []] cs y :=
  fun h => not_reach_aux h (.inr rfl)

theorem not_opEquivP_call_inline :
    ¬ OpEquivP H [.op (.call ⟨1⟩) []] [.op (.intConst .i32 42) []] := by
  intro h
  obtain ⟨y, hy⟩ := reach_call (H := H) fun _ _ _ _ => False
  exact not_reach_const (((h _ _ _ _ _).2.2 y).mp hy)

/-! ## The bodies of function `0` in the two stores -/

/-- Function `0` of `s` is Wasm code whose body satisfies `b`. -/
def body0B (s : Store Empty) (b : List Instr → Bool) : Bool :=
  match s.funcs[0]? with
  | some fi =>
    match fi.code with
    | .wasm fn => b fn.body
    | .host _ => false
  | none => false

/-- The body is `call 1`. -/
def isCall1 : List Instr → Bool
  | [.call x] => x == ⟨1⟩
  | _ => false

/-- The body is `i32.const 42`. -/
def isConst42 : List Instr → Bool
  | [.intConst .i32 c] => c == 42
  | _ => false

theorem body0B_sound {s : Store Empty} {b : List Instr → Bool} (h : body0B s b = true) :
    ∃ (fi : FuncInst Empty) (fn : Func), s.funcs[0]? = some fi ∧ fi.code = .wasm fn ∧
      b fn.body = true := by
  unfold body0B at h
  split at h
  · rename_i fi hfi
    split at h
    · rename_i fn hc
      exact ⟨fi, fn, hfi, hc, h⟩
    · cases h
  · cases h

theorem isCall1_sound {l : List Instr} (h : isCall1 l = true) : l = [.call ⟨1⟩] := by
  unfold isCall1 at h
  split at h
  · simp only [beq_iff_eq] at h
    rw [h]
  · cases h

theorem isConst42_sound {l : List Instr} (h : isConst42 l = true) :
    l = [.intConst .i32 42] := by
  unfold isConst42 at h
  split at h
  · simp only [beq_iff_eq] at h
    rw [h]
  · cases h

theorem callStore_body0B : body0B callStore isCall1 = true := by decide +kernel
theorem inlineStore_body0B : body0B inlineStore isConst42 = true := by decide +kernel

/-- Function `0` of `callStore` is Wasm code whose lifted body is `[call 1]`. -/
theorem callStore_body :
    ∃ (fi : FuncInst Empty) (fn : Func), callStore.funcs[0]? = some fi ∧ fi.code = .wasm fn ∧
      liftInstrs fn.body = [.op (.call ⟨1⟩) []] := by
  obtain ⟨fi, fn, hfi, hc, hb⟩ := body0B_sound callStore_body0B
  exact ⟨fi, fn, hfi, hc, by rw [isCall1_sound hb]; rfl⟩

/-- Function `0` of `inlineStore` is Wasm code whose lifted body is `[i32.const 42]`. -/
theorem inlineStore_body :
    ∃ (fi : FuncInst Empty) (fn : Func), inlineStore.funcs[0]? = some fi ∧
      fi.code = .wasm fn ∧ liftInstrs fn.body = [.op (.intConst .i32 42) []] := by
  obtain ⟨fi, fn, hfi, hc, hb⟩ := body0B_sound inlineStore_body0B
  exact ⟨fi, fn, hfi, hc, by rw [isConst42_sound hb]; rfl⟩

end Silmaril.Proofs.Wasm.Abstract.PubOpenWitness
