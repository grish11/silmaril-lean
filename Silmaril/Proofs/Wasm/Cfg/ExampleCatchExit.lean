module

public import Silmaril.Wasm.Cfg.ExampleCatchExit.Defs
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Cfg.Region.Thms
public import Silmaril.Proofs.Wasm.Cfg.Region
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

/-!
# Leaving the function through a caught exception: regression fixtures (proofs)
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleCatchExit

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Cfg.ExampleCatchExit

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem catchMod_valid : (Validation.validate? catchMod).isSome = true := by decide +kernel

theorem val_i32 (k : BitVec 32) : (Admin.plain (.intConst .i32 k)).val? = some (.i32 k) := rfl

/-- The exception `throw 0` allocates, with the payload `3, 4`. -/
abbrev exn34 (ta : Nat) : ExnInst := ⟨ta, [.i32 3, .i32 4]⟩

section Tag

variable {s : Store H} {f : Frame} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}
  (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
  (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 2)

include hmod hti in
theorem tag_t0 : s.tag? f t0 = some (ta, ti) := by
  have h0 : t0.toNat = 0 := rfl
  simp only [Store.tag?, h0, hmod]
  show (s.tags[ta]?.bind fun t => some (ta, t)) = _
  rw [hti]
  rfl

include hmod hti hexp hts in
/-- `throw 0` on the payload `3, 4` throws the new exception. -/
theorem run_throw (vs : List Val) :
    RunC P host C s f (vs ++ [.i32 3] ++ [.i32 4]) [.plain (.throw t0)] (s.addExn (exn34 ta)) f
      (.throw s.exns.length) := by
  simpa [List.append_assoc, exn34] using
    (RunC.throw (P := P) (host := host) (C := C) (ws := vs) (vs := [.i32 3, .i32 4]) (code := [])
      (tag_t0 hmod hti) hexp (by simp [hts]))

include hmod hti hexp hts in
/-- `i32.const 3; i32.const 4; throw 0` throws the new exception. -/
theorem run_tryBody {vs : List Val} :
    RunC P host C s f vs (expression tryBody) (s.addExn (exn34 ta)) f (.throw s.exns.length) :=
  .val (val_i32 3) (.val (val_i32 4) (run_throw hmod hti hexp hts vs))

include hmod in
/-- The clause `catch 0 l` catches it, with the payload. -/
theorem catches_exn (l : LabelIdx) :
    Catches (s.addExn (exn34 ta)) f s.exns.length [.catch_ t0 l] (some ([.i32 3, .i32 4], l)) :=
  .catch_ (e := exn34 ta) (by simp [Store.addExn]) hmod

/-! ## The machine: the exit stack is the whole frame stack -/

include hmod hti hexp hts

/-- The `try_table` frame of `bodyCatch`: arity `0`, the outer value `1`. -/
abbrev tryOne : LFrame := ⟨0, [.i32 1], false, true, [.catch_ t0 l0], .empty⟩

/-- **`bodyCatch`: the exit stack is `1, 3, 4`.** -/
theorem machine_catch :
    Relation.ReflTransGen (MStepC P host C bodyCatch) (initial bodyCatch s f)
      ⟨.exit, [.i32 1, .i32 3, .i32 4], [], s.addExn (exn34 ta), f⟩ := by
  have h₁ := MStepC.enter (P := P) (host := host) (C := C) (body := bodyCatch) (b := ⟨[], 0⟩)
    (sg := ⟨[.intConst .i32 1], some (.tryTable .empty [.catch_ t0 l0] tryBody)⟩) (stk := [])
    (stk₁ := [.i32 1]) (ws := [.i32 1]) (us := []) (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f)
    (a := 0) (c := tryBody) (bt := .empty) (t₁ := []) (t₂ := []) (loop := false) (tryT := true)
    (cs := [.catch_ t0 l0]) rfl rfl rfl .tryTable
    (by simpa [expression] using (RunC.val (val_i32 1) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 1)] s f (.normal [.i32 1])))
    (by
      have := CondArm.plain (i := Instr.tryTable .empty [.catch_ t0 l0] tryBody) (ws := [.i32 1])
        (us := []) (by simp)
      simpa using this) rfl rfl
  refine .head h₁ (.single ?_)
  exact MStepC.catchOut (b := ⟨[(0, 0)], 0⟩) (sg := ⟨[.intConst .i32 3, .intConst .i32 4], some (.throw t0)⟩)
    (stk₁ := [.i32 3, .i32 4]) (j := 0) (L := tryOne) (l := l0) rfl rfl trivial
    (.val (val_i32 3) (.val (val_i32 4) .nil))
    (by simpa using run_throw (P := P) (host := host) (C := C) hmod hti hexp hts [])
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) rfl rfl (catches_exn hmod l0) rfl

/-- The block frame of `bodyCatchNest`: arity `0`, the outer value `1`. -/
abbrev blkOne : LFrame := ⟨0, [.i32 1], false, false, [], .empty⟩

/-- The `try_table` frame of `bodyCatchNest`: arity `0`, the outer value `2`. -/
abbrev tryTwo : LFrame := ⟨0, [.i32 2], false, true, [.catch_ t0 l1], .empty⟩

/-- **`bodyCatchNest`: the exit stack is the whole frame stack `1, 2, 3, 4`.** -/
theorem machine_catchNest :
    Relation.ReflTransGen (MStepC P host C bodyCatchNest) (initial bodyCatchNest s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3, .i32 4], [], s.addExn (exn34 ta), f⟩ := by
  have h₁ := MStepC.enter (P := P) (host := host) (C := C) (body := bodyCatchNest)
    (b := ⟨[], 0⟩) (sg := ⟨[.intConst .i32 1], some (.block .empty innerNest)⟩) (stk := [])
    (stk₁ := [.i32 1]) (ws := [.i32 1]) (us := []) (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f)
    (a := 0) (c := innerNest) (bt := .empty) (t₁ := []) (t₂ := []) (loop := false) (tryT := false)
    (cs := []) rfl rfl rfl .block
    (by simpa [expression] using (RunC.val (val_i32 1) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 1)] s f (.normal [.i32 1])))
    (by
      have := CondArm.plain (i := Instr.block .empty innerNest) (ws := [.i32 1]) (us := [])
        (by simp)
      simpa using this) rfl rfl
  have h₂ := MStepC.enter (P := P) (host := host) (C := C) (body := bodyCatchNest)
    (b := ⟨[(0, 0)], 0⟩) (sg := ⟨[.intConst .i32 2], some (.tryTable .empty [.catch_ t0 l1] tryBody)⟩)
    (stk := []) (stk₁ := [.i32 2]) (ws := [.i32 2]) (us := []) (ls := [blkOne]) (s := s) (s₁ := s)
    (f := f) (f₁ := f) (a := 0) (c := tryBody) (bt := .empty) (t₁ := []) (t₂ := []) (loop := false)
    (tryT := true) (cs := [.catch_ t0 l1]) rfl rfl rfl .tryTable
    (by simpa [expression] using (RunC.val (val_i32 2) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 2)] s f (.normal [.i32 2])))
    (by
      have := CondArm.plain (i := Instr.tryTable .empty [.catch_ t0 l1] tryBody) (ws := [.i32 2])
        (us := []) (by simp)
      simpa using this) rfl rfl
  refine .head h₁ (.head h₂ (.single ?_))
  exact MStepC.catchOut (b := ⟨[(0, 0), (0, 0)], 0⟩)
    (sg := ⟨[.intConst .i32 3, .intConst .i32 4], some (.throw t0)⟩)
    (stk₁ := [.i32 3, .i32 4]) (j := 0) (L := tryTwo) (l := l1) (ls := [tryTwo, blkOne]) rfl rfl
    trivial (.val (val_i32 3) (.val (val_i32 4) .nil))
    (by simpa using run_throw (P := P) (host := host) (C := C) hmod hti hexp hts [])
    (fun _ _ h => absurd h (Nat.not_lt_zero _)) rfl rfl (catches_exn hmod l1) rfl

/-! ## Core: the function returns the payload -/

/-- **`bodyCatch` returns `3, 4` in Core 3.0.** -/
theorem core_catch (g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyCatch)]]⟩
      ⟨s.addExn (exn34 ta), g, vals [.i32 3, .i32 4]⟩ := by
  have hr : Region.Run P host s f [] [.label 2 [] (expression bodyCatch)] (s.addExn (exn34 ta)) f
      (.normal [.i32 3, .i32 4]) := by
    refine RunC.labelBr0 (us₁ := [.i32 1]) (us₂ := [.i32 3, .i32 4]) ?_ rfl
      (by simpa [expression] using (Proofs.Region.run_vals_normal (P := P) (host := host)
        (C := noCall) (s := s.addExn (exn34 ta)) (f := f) [.i32 3, .i32 4]))
    refine .val (val_i32 1) (.tryTable (ws := [.i32 1]) (us := []) (t₁ := []) (t₂ := []) rfl rfl ?_)
    exact RunC.handlerCatch (vs := [.i32 1]) (us := [.i32 3, .i32 4]) (l := l0)
      (code := [.plain .unreachable]) (n := 0)
      (RunC.labelThrow (vs := []) (n := 0) (cont := []) (code := []) (by
        simpa [vals] using run_tryBody (P := P) (host := host) (C := noCall) (vs := []) hmod hti hexp
          hts))
      (catches_exn hmod l0)
  obtain ⟨c', hs, he⟩ := Region.run_sound hr
  simp only [Out.Ends] at he; subst he
  exact (Proofs.Region.steps_frame (f := g) 2 (by simpa [vals] using hs)).tail
    (Step.frameVals (P := P) (host := host) rfl)

/-- **`bodyCatchNest` returns `3, 4` in Core 3.0.** -/
theorem core_catchNest (g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyCatchNest)]]⟩
      ⟨s.addExn (exn34 ta), g, vals [.i32 3, .i32 4]⟩ := by
  have hr : Region.Run P host s f [] [.label 2 [] (expression bodyCatchNest)]
      (s.addExn (exn34 ta)) f (.normal [.i32 3, .i32 4]) := by
    refine RunC.labelBr0 (us₁ := [.i32 1, .i32 2]) (us₂ := [.i32 3, .i32 4]) ?_ rfl
      (by simpa [expression] using (Proofs.Region.run_vals_normal (P := P) (host := host)
        (C := noCall) (s := s.addExn (exn34 ta)) (f := f) [.i32 3, .i32 4]))
    refine .val (val_i32 1) (.block (ws := [.i32 1]) (us := []) (t₁ := []) (t₂ := []) rfl rfl ?_)
    have hin : Region.Run P host s f [] (expression innerNest) (s.addExn (exn34 ta)) f
        (.br 1 [.i32 2, .i32 3, .i32 4]) := by
      refine .val (val_i32 2) (.tryTable (ws := [.i32 2]) (us := []) (t₁ := []) (t₂ := []) rfl rfl ?_)
      exact RunC.handlerCatch (vs := [.i32 2]) (us := [.i32 3, .i32 4]) (l := l1)
        (code := [.plain .drop]) (n := 0)
        (RunC.labelThrow (vs := []) (n := 0) (cont := []) (code := []) (by
          simpa [vals] using run_tryBody (P := P) (host := host) (C := noCall) (vs := []) hmod hti
            hexp hts))
        (catches_exn hmod l1)
    simpa using RunC.labelBrSucc (vs := [.i32 1]) (n := 0) (l := 0) (cont := [])
      (code := [.plain .unreachable]) hin
  obtain ⟨c', hs, he⟩ := Region.run_sound hr
  simp only [Out.Ends] at he; subst he
  exact (Proofs.Region.steps_frame (f := g) 2 (by simpa [vals] using hs)).tail
    (Step.frameVals (P := P) (host := host) rfl)

end Tag

/-- **The tag hypotheses hold at the instance of `catchMod`**: tag `0` of the functions' module
is a tag of the store whose type expands to `[i32 i32] → []`. -/
theorem catch_tag : ∃ (ta : Nat) (ti : TagInst) (ts : Validation.Ty (.list .val)),
    catchMI.tags[0]? = some ta ∧ catchStore.tags[ta]? = some ti ∧
    Validation.Expand ti.type (.func ts .nil) ∧ ts.length = 2 :=
  ⟨_, _, _, rfl, rfl, Validation.Expand.iff.2 rfl, rfl⟩

end Silmaril.Wasm.Cfg.Proofs.ExampleCatchExit
