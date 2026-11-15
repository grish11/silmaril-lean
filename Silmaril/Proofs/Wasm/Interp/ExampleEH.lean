module

public import Silmaril.Wasm.Interp.ExampleEH.Defs
public import Silmaril.Proofs.Wasm.Interp.EHSim

/-!
# A caught exception (proofs)

`eh_run`: the native run of `ehBody`, through `throw`, the first-match catch and the block.
`eh_steps`: by `evalOXE_goodEH`, it is a Core 3.0 run from the code to the value `7`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Interp.ExampleEH

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallXE Silmaril.Wasm.Interp Silmaril.Wasm.Interp.ExampleEH

variable {P : Numerics.Profile} {host : HostSemantics Empty}

theorem ehTag_expand : ∃ ts : Validation.Ty (.list .val),
    Validation.Expand ehTag.type (.func ts .nil) ∧ ts.length = 1 :=
  ⟨_, Validation.Expand.iff.mpr rfl, rfl⟩

/-- The arguments of the `throw`. -/
theorem eh_args : EvalOXE ehC ehStore ehFrame [] [.op (.intConst .i32 7) []]
    (ehStore, ehFrame, .normal [v7]) :=
  .opOk (fun _ h => by cases h) .nil rfl .nil

/-- The `throw`: the exception `0` with the field `7`. -/
theorem eh_throw : EvalOXE ehC ehStore ehFrame [] [.op (.throw ⟨0⟩) [.op (.intConst .i32 7) []]]
    (ehStore', ehFrame, .throw 0) := by
  obtain ⟨ts, he, hn⟩ := ehTag_expand
  have h := EvalOXE.throw (C := ehC) (x := ⟨0⟩) (ta := 0) (ti := ehTag) (es := []) eh_args
    (by rfl) he (by simp [hn])
  simp only [hn] at h
  exact h

/-- **The native run**: the exception is thrown, caught by `catch $t 0`, and the block produces
`7`. -/
theorem eh_run : EvalOXE ehC ehStore ehFrame [] ehBody (ehStore', ehFrame, .normal [v7]) :=
  .blockOk (np := 0) (nr := 1) rfl
    (.tryCatch (np := 0) (nr := 0) rfl eh_throw (.catch_ (e := ⟨0, [v7]⟩) rfl rfl))
    rfl .nil

/-! ## The Core run -/

theorem ehC_sound : OracleSoundE (ehExt ehTags) P host ehC true := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ h
  exact h.elim

theorem ehC_throws : OracleThrowsE (ehExt ehTags) P host ehC := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  exact h.elim

theorem ehC_tags : OracleTagsE ehTags ehC := by
  intro _ _ _ _ _ h
  exact h.elim

theorem eh_tagsOk : TagsOk ehTags ehStore :=
  ⟨rfl, fun a e h => by simp [ehStore] at h⟩

theorem eh_storeChk : StoreChkE (ehExt ehTags) ehStore.funcs := by
  intro a fi fn ps rs h
  simp [ehStore] at h

/-- The code passes the exception checker: the block produces one value. -/
theorem eh_chk : chkE (ehExt ehTags) ehStore.funcs ehMod 0 0 [] (some 0) ehBody = some (some 1) := by
  decide

/-- **The Core 3.0 run**: from the code, through `throw` and the handler's first-match catch, to
the value `7`, in the store holding the exception, at every profile and host. -/
theorem eh_steps : Steps P host ⟨ehStore, ehFrame, expression (Binaryen.BExpr.lowerList ehBody)⟩
    ⟨ehStore', ehFrame, vals [v7]⟩ := by
  obtain ⟨-, -, hc⟩ := evalOXE_goodEH ehC_sound ehC_throws ehC_tags eh_run rfl eh_tagsOk
  obtain ⟨c', o, hst, he, hm⟩ := run_of_wp (hc eh_storeChk eh_chk)
  rw [ends_normal hm he] at hst
  simpa using hst

/-! ## Rethrow through `catch_ref` and `throw_ref` -/

/-- **The native run of the rethrow**: `catch_ref` catches with the field and the reference, the
block keeps the reference, and `throw_ref` throws the exception `0` again. -/
theorem eh2_run : EvalOXE ehC ehStore ehFrame [] ehBody2 (ehStore', ehFrame, .throw 0) :=
  .blockOk (np := 0) (nr := 1) rfl
    (.tryCatch (np := 0) (nr := 0) rfl eh_throw (.catchRef (e := ⟨0, [v7]⟩) rfl rfl))
    rfl (.throwRefExn .nil)

theorem eh2_chk : chkE (ehExt ehTags) ehStore.funcs ehMod 0 0 [] (some 0) ehBody2 = some none := by
  decide

/-- **The Core 3.0 run of the rethrow**: from the code to the thrown exception `0`
(`REF.EXN_ADDR 0; THROW_REF`), at every profile and host. -/
theorem eh2_steps : Steps P host ⟨ehStore, ehFrame, expression (Binaryen.BExpr.lowerList ehBody2)⟩
    ⟨ehStore', ehFrame, throwing 0⟩ := by
  obtain ⟨-, -, hc⟩ := evalOXE_goodEH ehC_sound ehC_throws ehC_tags eh2_run rfl eh_tagsOk
  obtain ⟨c', o, hst, he, hm⟩ := run_of_wp (hc eh_storeChk eh2_chk)
  rcases o with _ | _ | _ | _ | a | _ | _ <;> simp only [FlowMatch] at hm
  subst hm
  have hc' : c' = throwing 0 := he
  exact hc' ▸ hst

/-! ## Multi-value parameters of `if` and `try_table` -/

theorem const_run {s : Store Empty} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    {r : Store Empty × Frame × Binaryen.Flow} {b : BitVec 32}
    (h : EvalOXE ehC s f (Binaryen.ofInt .i32 b :: stk) es r) :
    EvalOXE ehC s f stk (.op (.intConst .i32 b) [] :: es) r :=
  .opOk (fun _ h => by cases h) .nil rfl h

/-- The `if` with two parameters: the condition `1` selects `i32.add`, `1 + 2 = 3`; the code
after it runs on `3`. -/
theorem eh3_if {es : List Binaryen.BExpr} {r : Store Empty × Frame × Binaryen.Flow}
    (hk : EvalOXE ehC ehStore ehFrame3 [v3] es r) :
    EvalOXE ehC ehStore ehFrame3 [Binaryen.ofInt .i32 2, Binaryen.ofInt .i32 1]
      (.if_ (.typeIdx ⟨0⟩) [.op (.intConst .i32 1) []] [.op (.intBinOp .i32 .add) []]
        [.op (.intBinOp .i32 .sub) []] :: es) r :=
  .ifOk (b := true) (np := 2) (nr := 1) (const_run .nil) rfl rfl
    (.opOk (fun _ h => by cases h) .nil rfl .nil) rfl hk

/-- The `try_table` body: `drop`, then `throw $t` with the remaining parameter `3`. -/
theorem eh3_throw : EvalOXE ehC ehStore ehFrame3 [Binaryen.ofInt .i32 4, v3]
    [.op .drop [], .op (.throw ⟨0⟩) []] (ehStore3, ehFrame3, .throw 0) := by
  obtain ⟨ts, he, hn⟩ := ehTag_expand
  have h := EvalOXE.throw (C := ehC) (s := ehStore) (f := ehFrame3) (stk := [v3]) (x := ⟨0⟩)
    (ta := 0) (ti := ehTag) (es := []) .nil (by rfl) he (by simp [hn])
  simp only [hn] at h
  exact .opOk (fun _ h => by cases h) .nil rfl h

/-- **The native multi-value run**: the `if` consumes two parameters and produces `3`; the
`try_table` consumes `4` and `3`, throws `3`, and the clause branches out of the block with it. -/
theorem eh3_run : EvalOXE ehC ehStore ehFrame3 [] ehBody3 (ehStore3, ehFrame3, .normal [v3]) :=
  .blockOk (np := 0) (nr := 1) rfl
    (const_run (const_run (eh3_if (const_run
      (.tryCatch (np := 2) (nr := 1) rfl eh3_throw (.catch_ (e := ⟨0, [v3]⟩) rfl rfl))))))
    rfl .nil

theorem eh3_chk : chkE (ehExt ehTags) ehStore.funcs ehMod3 0 0 [] (some 0) ehBody3 = some (some 1) := by
  decide

/-- **The Core 3.0 multi-value run**: from the code to the value `3`, at every profile and host. -/
theorem eh3_steps : Steps P host ⟨ehStore, ehFrame3, expression (Binaryen.BExpr.lowerList ehBody3)⟩
    ⟨ehStore3, ehFrame3, vals [v3]⟩ := by
  obtain ⟨-, -, hc⟩ := evalOXE_goodEH ehC_sound ehC_throws ehC_tags eh3_run rfl eh_tagsOk
  obtain ⟨c', o, hst, he, hm⟩ := run_of_wp (hc eh_storeChk eh3_chk)
  rw [ends_normal hm he] at hst
  simpa using hst

end Silmaril.Proofs.Wasm.Interp.ExampleEH
