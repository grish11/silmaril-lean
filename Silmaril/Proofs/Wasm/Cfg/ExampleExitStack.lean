module

public import Silmaril.Wasm.Cfg.ExampleExitStack.Defs
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Cfg.Region.Thms
public import Silmaril.Proofs.Wasm.Cfg.Region
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

/-!
# Leaving the function from inside a block: regression fixtures (proofs)
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleExitStack

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Cfg.ExampleExitStack

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem exitMod_valid : (Validation.validate? exitMod).isSome = true := by decide +kernel

theorem lossMod_invalid :
    (Validation.validate? ({ types := [resI32x2], funcs := [⟨⟨0⟩, [], bodyLoss⟩] } : Module)).isSome =
      false := by decide +kernel

theorem val_i32 (k : BitVec 32) : (Admin.plain (.intConst .i32 k)).val? = some (.i32 k) := rfl

/-! ## The machine: the exit stack is the whole frame stack -/

/-- The machine enters the block of `ret` with the outer value `1`. -/
theorem enter_ret {s : Store H} {f : Frame} :
    MStepC P host C bodyRet (initial bodyRet s f) ⟨.block ⟨[(0, 0)], 0⟩, [], [frameOne], s, f⟩ := by
  have h := MStepC.enter (P := P) (host := host) (C := C) (body := bodyRet) (b := ⟨[], 0⟩)
    (sg := ⟨[.intConst .i32 1], some (.block .empty innerRet)⟩) (stk := []) (stk₁ := [.i32 1])
    (ws := [.i32 1]) (us := []) (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f) (a := 0) (c := innerRet)
    (bt := .empty) (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := []) rfl rfl rfl
    .block (by simpa [expression] using (RunC.val (val_i32 1) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 1)] s f (.normal [.i32 1])))
    (by
      have := CondArm.plain (i := Instr.block .empty innerRet) (ws := [.i32 1]) (us := []) (by simp)
      simpa using this) rfl rfl
  exact h

/-- The machine enters the block of `br` with the outer value `1`. -/
theorem enter_br {s : Store H} {f : Frame} :
    MStepC P host C bodyBr (initial bodyBr s f) ⟨.block ⟨[(0, 0)], 0⟩, [], [frameOne], s, f⟩ := by
  have h := MStepC.enter (P := P) (host := host) (C := C) (body := bodyBr) (b := ⟨[], 0⟩)
    (sg := ⟨[.intConst .i32 1], some (.block .empty innerBr)⟩) (stk := []) (stk₁ := [.i32 1])
    (ws := [.i32 1]) (us := []) (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f) (a := 0) (c := innerBr)
    (bt := .empty) (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := []) rfl rfl rfl
    .block (by simpa [expression] using (RunC.val (val_i32 1) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 1)] s f (.normal [.i32 1])))
    (by
      have := CondArm.plain (i := Instr.block .empty innerBr) (ws := [.i32 1]) (us := []) (by simp)
      simpa using this) rfl rfl
  exact h

/-- The machine enters the block of `brIf` with the outer value `1`. -/
theorem enter_brIf {s : Store H} {f : Frame} :
    MStepC P host C (bodyBrIf 1) (initial (bodyBrIf 1) s f) ⟨.block ⟨[(0, 0)], 0⟩, [], [frameOne], s, f⟩ := by
  have h := MStepC.enter (P := P) (host := host) (C := C) (body := (bodyBrIf 1)) (b := ⟨[], 0⟩)
    (sg := ⟨[.intConst .i32 1], some (.block .empty (innerBrIf 1))⟩) (stk := []) (stk₁ := [.i32 1])
    (ws := [.i32 1]) (us := []) (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f) (a := 0) (c := (innerBrIf 1))
    (bt := .empty) (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := []) rfl rfl rfl
    .block (by simpa [expression] using (RunC.val (val_i32 1) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 1)] s f (.normal [.i32 1])))
    (by
      have := CondArm.plain (i := Instr.block .empty (innerBrIf 1)) (ws := [.i32 1]) (us := []) (by simp)
      simpa using this) rfl rfl
  exact h

/-- The machine enters the block of `table` with the outer value `1`. -/
theorem enter_table {s : Store H} {f : Frame} :
    MStepC P host C bodyTable (initial bodyTable s f) ⟨.block ⟨[(0, 0)], 0⟩, [], [frameOne], s, f⟩ := by
  have h := MStepC.enter (P := P) (host := host) (C := C) (body := bodyTable) (b := ⟨[], 0⟩)
    (sg := ⟨[.intConst .i32 1], some (.block .empty innerTable)⟩) (stk := []) (stk₁ := [.i32 1])
    (ws := [.i32 1]) (us := []) (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f) (a := 0) (c := innerTable)
    (bt := .empty) (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := []) rfl rfl rfl
    .block (by simpa [expression] using (RunC.val (val_i32 1) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 1)] s f (.normal [.i32 1])))
    (by
      have := CondArm.plain (i := Instr.block .empty innerTable) (ws := [.i32 1]) (us := []) (by simp)
      simpa using this) rfl rfl
  exact h

/-- The machine enters the block of `loss` with the outer value `1`. -/
theorem enter_loss {s : Store H} {f : Frame} :
    MStepC P host C bodyLoss (initial bodyLoss s f) ⟨.block ⟨[(0, 0)], 0⟩, [], [frameOne], s, f⟩ := by
  have h := MStepC.enter (P := P) (host := host) (C := C) (body := bodyLoss) (b := ⟨[], 0⟩)
    (sg := ⟨[.intConst .i32 1], some (.block .empty innerLoss)⟩) (stk := []) (stk₁ := [.i32 1])
    (ws := [.i32 1]) (us := []) (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f) (a := 0) (c := innerLoss)
    (bt := .empty) (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := []) rfl rfl rfl
    .block (by simpa [expression] using (RunC.val (val_i32 1) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 1)] s f (.normal [.i32 1])))
    (by
      have := CondArm.plain (i := Instr.block .empty innerLoss) (ws := [.i32 1]) (us := []) (by simp)
      simpa using this) rfl rfl
  exact h

/-- **`bodyRet`: the exit stack is `1, 2, 3`.** -/
theorem machine_ret (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyRet) (initial bodyRet s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ := by
  refine .head enter_ret (.single ?_)
  exact MStepC.ret (sg := ⟨[.intConst .i32 2, .intConst .i32 3], some .return_⟩) rfl rfl
    (.val (val_i32 2) (.val (val_i32 3) .nil))

/-- **`bodyBr`: the exit stack is `1, 2, 3`.** -/
theorem machine_br (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyBr) (initial bodyBr s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ := by
  refine .head enter_br (.single ?_)
  exact MStepC.brOut (sg := ⟨[.intConst .i32 2, .intConst .i32 3], some (.br l1)⟩) rfl rfl
    (.val (val_i32 2) (.val (val_i32 3) .nil)) rfl

/-- **`bodyBrIf 1` (taken): the exit stack is `1, 2, 3`.** -/
theorem machine_brIf_taken (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C (bodyBrIf 1)) (initial (bodyBrIf 1) s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ := by
  refine .head enter_brIf (.single ?_)
  exact MStepC.brIfOut (sg := ⟨[.intConst .i32 2, .intConst .i32 3, .intConst .i32 1], some (.brIf l1)⟩)
    (stk₁ := [.i32 2, .i32 3]) (k := 1) rfl rfl
    (.val (val_i32 2) (.val (val_i32 3) (.val (val_i32 1) .nil))) (by decide) rfl

/-- **`bodyTable`: the exit stack is `1, 2, 3`.** -/
theorem machine_table (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyTable) (initial bodyTable s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ := by
  refine .head enter_table (.single ?_)
  exact MStepC.brDataOut
    (sg := ⟨[.intConst .i32 2, .intConst .i32 3, .intConst .i32 0], some (.brTable [l1] l1)⟩)
    (ws := [.i32 2, .i32 3]) (us := [.i32 0]) (us' := []) (l := l1) rfl rfl
    (.val (val_i32 2) (.val (val_i32 3) (.val (val_i32 0) .nil))) (.tableLt rfl) rfl

/-- **`bodyLoss`: the exit stack is `1, 2`** (the outer value is kept). -/
theorem machine_loss (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyLoss) (initial bodyLoss s f)
      ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ := by
  refine .head enter_loss (.single ?_)
  exact MStepC.ret (sg := ⟨[.intConst .i32 2], some .return_⟩) rfl rfl (.val (val_i32 2) .nil)

/-- The machine enters the block of `brIf0` with the outer value `1`. -/
theorem enter_brIf0 {s : Store H} {f : Frame} :
    MStepC P host C (bodyBrIf 0) (initial (bodyBrIf 0) s f) ⟨.block ⟨[(0, 0)], 0⟩, [], [frameOne], s, f⟩ := by
  have h := MStepC.enter (P := P) (host := host) (C := C) (body := bodyBrIf 0) (b := ⟨[], 0⟩)
    (sg := ⟨[.intConst .i32 1], some (.block .empty (innerBrIf 0))⟩) (stk := []) (stk₁ := [.i32 1])
    (ws := [.i32 1]) (us := []) (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f) (a := 0)
    (c := innerBrIf 0) (bt := .empty) (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := [])
    rfl rfl rfl .block (by simpa [expression] using (RunC.val (val_i32 1) .nil :
      RunC P host C s f [] [.plain (.intConst .i32 1)] s f (.normal [.i32 1])))
    (by
      have := CondArm.plain (i := Instr.block .empty (innerBrIf 0)) (ws := [.i32 1]) (us := []) (by simp)
      simpa using this) rfl rfl
  exact h

theorem drop_run {s : Store H} {f : Frame} (v : Val) (vs : List Val) {code : List Admin} {o : Out}
    (h : RunC P host C s f vs code s f o) :
    RunC P host C s f (vs ++ [v]) (.plain .drop :: code) s f o := by
  have := Proofs.Region.step_in (P := P) (host := host) vs [] (Step.parametric (ParametricStep.drop v))
    (s := s) (f := f)
  exact .simple (vs₁ := vs) (by simp [SingleThreaded.Det.famOf]) (.single (by simpa [vals] using this)) h

/-- **`bodyBrIf 0` (not taken): the machine falls through both sequences and exits with `4, 5`.** -/
theorem machine_brIf_not (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C (bodyBrIf 0)) (initial (bodyBrIf 0) s f)
      ⟨.exit, [.i32 4, .i32 5], [], s, f⟩ := by
  refine .head enter_brIf0 (.head (MStepC.brIfNot
    (sg := ⟨[.intConst .i32 2, .intConst .i32 3, .intConst .i32 0], some (.brIf l1)⟩)
    (stk₁ := [.i32 2, .i32 3]) rfl rfl (.val (val_i32 2) (.val (val_i32 3) (.val (val_i32 0) .nil))))
    (.head (MStepC.fall (sg := ⟨[.drop, .drop], none⟩) (stk₁ := []) rfl rfl
      (drop_run (.i32 3) [.i32 2] (drop_run (.i32 2) [] .nil))) (.single ?_)))
  exact MStepC.fall (sg := ⟨[.drop, .intConst .i32 4, .intConst .i32 5], none⟩)
    (stk₁ := [.i32 4, .i32 5]) rfl rfl (drop_run (.i32 1) [] (.val (val_i32 4) (.val (val_i32 5) .nil)))

/-! ## Core: the function returns its top values -/

/-- A region run of a function body that returns: the function's frame returns its top `n`
values. -/
theorem frame_of_ret {s : Store H} {f g : Frame} {code : List Admin} {W vs : List Val} {n : Nat}
    (h : Region.Run P host s f [] code s f (.ret (W ++ vs))) (hn : vs.length = n) :
    Steps P host ⟨s, g, [.frame n f [.label n [] code]]⟩ ⟨s, g, vals vs⟩ := by
  obtain ⟨c', hs, rest, rfl⟩ := Region.run_sound h
  have hl : Steps P host ⟨s, f, [.label n [] code]⟩
      ⟨s, f, vals (W ++ vs) ++ [.plain .return_]⟩ := by
    refine (Proofs.Region.steps_label n [] (by simpa using hs)).tail ?_
    simpa [List.append_assoc] using
      (Step.returnLabel (P := P) (host := host) (s := s) (f := f) (n := n) (cont := [])
        (vs := W ++ vs) (rest := rest))
  refine (Proofs.Region.steps_frame (f := g) n hl).tail ?_
  simpa [vals_append, List.append_assoc] using
    (Step.returnFrame (P := P) (host := host) (s := s) (f := g) (fi := f) (n := n) (vs' := W)
      (vs := vs) (rest := []) hn)

/-- A region run of a function body that branches to the function label (or falls through):
the function's frame returns its top `n` values. -/
theorem frame_of_label {s : Store H} {f g : Frame} {code : List Admin} {vs : List Val} {n : Nat}
    (h : Region.Run P host s f [] [.label n [] code] s f (.normal vs)) (hn : vs.length = n) :
    Steps P host ⟨s, g, [.frame n f [.label n [] code]]⟩ ⟨s, g, vals vs⟩ := by
  obtain ⟨c', hs, he⟩ := Region.run_sound h
  simp only [Out.Ends] at he; subst he
  exact (Proofs.Region.steps_frame (f := g) n (by simpa [vals] using hs)).tail
    (Step.frameVals (P := P) (host := host) hn)

theorem run_inner2 {s : Store H} {f : Frame} {code : List Admin} {o : Out}
    (h : Region.Run P host s f [.i32 2, .i32 3] code s f o) :
    Region.Run P host s f [] (.plain (.intConst .i32 2) :: .plain (.intConst .i32 3) :: code) s f o :=
  .val (val_i32 2) (.val (val_i32 3) h)

/-- **`bodyRet` returns `2, 3` in Core 3.0.** -/
theorem core_ret (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyRet)]]⟩ ⟨s, g, vals [.i32 2, .i32 3]⟩ := by
  refine frame_of_ret (W := [.i32 1]) ?_ rfl
  refine .val (val_i32 1) (.block (ws := [.i32 1]) (us := []) (t₁ := []) (t₂ := []) rfl rfl ?_)
  simpa using RunC.labelRet (vs := [.i32 1]) (n := 0) (cont := []) (code := [.plain (.intConst .i32 4)])
    (by simpa [expression, innerRet] using run_inner2 (code := [.plain .return_]) .ret)

/-- **`bodyLoss` returns `1, 2` in Core 3.0**: the returned values reach below the block. -/
theorem core_loss (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyLoss)]]⟩ ⟨s, g, vals [.i32 1, .i32 2]⟩ := by
  refine frame_of_ret (W := []) ?_ rfl
  refine .val (val_i32 1) (.block (ws := [.i32 1]) (us := []) (t₁ := []) (t₂ := []) rfl rfl ?_)
  simpa using RunC.labelRet (vs := [.i32 1]) (n := 0) (cont := []) (code := [])
    (by simpa [expression, innerLoss] using
      (RunC.val (val_i32 2) .ret : Region.Run P host s f [] [.plain (.intConst .i32 2), .plain .return_] s f _))

/-- **`bodyBr` returns `2, 3` in Core 3.0.** -/
theorem core_br (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyBr)]]⟩ ⟨s, g, vals [.i32 2, .i32 3]⟩ := by
  refine frame_of_label ?_ rfl
  refine RunC.labelBr0 (us₁ := [.i32 1]) (us₂ := [.i32 2, .i32 3]) ?_ rfl
    (by simpa [expression] using (Proofs.Region.run_vals_normal (P := P) (host := host)
      (C := noCall) (s := s) (f := f) [.i32 2, .i32 3]))
  refine .val (val_i32 1) (.block (ws := [.i32 1]) (us := []) (t₁ := []) (t₂ := []) rfl rfl ?_)
  simpa [expression, innerBr] using RunC.labelBrSucc (vs := [.i32 1]) (n := 0) (cont := [])
    (code := [.plain (.intConst .i32 4)]) (run_inner2 (code := [.plain (.br l1)]) .br)

/-- **`bodyBrIf 1` (taken) returns `2, 3` in Core 3.0.** -/
theorem core_brIf_taken (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression (bodyBrIf 1))]]⟩
      ⟨s, g, vals [.i32 2, .i32 3]⟩ := by
  refine frame_of_label ?_ rfl
  refine RunC.labelBr0 (us₁ := [.i32 1]) (us₂ := [.i32 2, .i32 3]) ?_ rfl
    (by simpa [expression] using (Proofs.Region.run_vals_normal (P := P) (host := host)
      (C := noCall) (s := s) (f := f) [.i32 2, .i32 3]))
  refine .val (val_i32 1) (.block (ws := [.i32 1]) (us := []) (t₁ := []) (t₂ := []) rfl rfl ?_)
  have hin : Region.Run P host s f [] (expression (innerBrIf 1)) s f (.br 1 [.i32 2, .i32 3]) :=
    run_inner2 (.val (val_i32 1) (.brIf (k := 1) (by
      simp only [show (1 : BitVec 32) ≠ 0 by decide, ↓reduceIte, List.singleton_append]
      exact RunC.br)))
  simpa [expression] using RunC.labelBrSucc (vs := [.i32 1]) (n := 0) (cont := [])
    (code := [.plain .drop, .plain (.intConst .i32 4), .plain (.intConst .i32 5)]) hin

/-- **`bodyTable` returns `2, 3` in Core 3.0.** -/
theorem core_table (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyTable)]]⟩
      ⟨s, g, vals [.i32 2, .i32 3]⟩ := by
  refine frame_of_label ?_ rfl
  refine RunC.labelBr0 (us₁ := [.i32 1]) (us₂ := [.i32 2, .i32 3]) ?_ rfl
    (by simpa [expression] using (Proofs.Region.run_vals_normal (P := P) (host := host)
      (C := noCall) (s := s) (f := f) [.i32 2, .i32 3]))
  refine .val (val_i32 1) (.block (ws := [.i32 1]) (us := []) (t₁ := []) (t₂ := []) rfl rfl ?_)
  have hin : Region.Run P host s f [] (expression innerTable) s f (.br 1 [.i32 2, .i32 3]) :=
    run_inner2 (.val (val_i32 0) (.brData (ws := [.i32 2, .i32 3]) (us := [.i32 0]) (us' := [])
      (.tableLt (l := l1) rfl) (by simp only [List.append_nil]; exact RunC.br)))
  simpa [expression] using RunC.labelBrSucc (vs := [.i32 1]) (n := 0) (cont := [])
    (code := [.plain (.intConst .i32 4)]) hin

/-- **`bodyBrIf 0` (not taken) returns `4, 5` in Core 3.0.** -/
theorem core_brIf_not (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression (bodyBrIf 0))]]⟩
      ⟨s, g, vals [.i32 4, .i32 5]⟩ := by
  refine frame_of_label ?_ rfl
  have hdrop : ∀ (v : Val) (vs : List Val), Steps P host ⟨s, f, vals (vs ++ [v]) ++ [.plain .drop]⟩
      ⟨s, f, vals vs⟩ := fun v vs => by
    have := Proofs.Region.step_in (P := P) (host := host) vs [] (Step.parametric (ParametricStep.drop v)) (s := s)
      (f := f)
    exact .single (by simpa [vals] using this)
  have hin : Region.Run P host s f [] (expression (innerBrIf 0)) s f (.normal []) :=
    run_inner2 (.val (val_i32 0) (.brIf (k := 0) (by
      simp only [↓reduceIte, List.nil_append]
      exact .simple (vs₁ := [.i32 2]) (by simp [SingleThreaded.Det.famOf]) (hdrop (.i32 3) [.i32 2])
        (.simple (vs₁ := []) (by simp [SingleThreaded.Det.famOf]) (hdrop (.i32 2) []) .nil))))
  have hout : Region.Run P host s f [.i32 1] [.plain .drop, .plain (.intConst .i32 4),
      .plain (.intConst .i32 5)] s f (.normal [.i32 4, .i32 5]) :=
    .simple (vs₁ := []) (by simp [SingleThreaded.Det.famOf]) (hdrop (.i32 1) [])
      (.val (val_i32 4) (.val (val_i32 5) .nil))
  refine RunC.labelNormal (vs := []) ?_ (by simpa using (RunC.nil : RunC P host noCall s f
    [.i32 4, .i32 5] [] s f _))
  refine .val (val_i32 1) (.block (ws := [.i32 1]) (us := []) (t₁ := []) (t₂ := []) rfl rfl ?_)
  exact RunC.labelNormal (vs := [.i32 1]) (by simpa using hin) (by simpa using hout)

end Silmaril.Wasm.Cfg.Proofs.ExampleExitStack
