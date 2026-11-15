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

end Silmaril.Proofs.Wasm.Interp.ExampleEH
