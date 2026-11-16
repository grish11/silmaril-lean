module

public import Silmaril.Wasm.Cfg.ExampleBrOut.Defs
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Cfg.Region.Thms
public import Silmaril.Proofs.Wasm.Cfg.Region
public import Silmaril.Wasm.Abstract.SelfLoop.Thms

@[expose] public section

/-!
# Branches to the function label: regression fixtures (proofs)
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleBrOut

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Cfg.ExampleBrOut

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem brOutMod_valid : (Validation.validate? brOutMod).isSome = true := by decide +kernel

/-- A segment of constants only pushes its values. -/
theorem run_consts : ∀ {is : List Instr} {s s' : Store H} {f f' : Frame} {vs : List Val}
    {o : Region.Out}, (∀ i ∈ is, (Admin.plain i).val? ≠ none) →
    RunC P host C s f vs (expression is) s' f' o →
    s' = s ∧ f' = f ∧ o = .normal (vs ++ is.filterMap fun i => (Admin.plain i).val?)
  | [], _, _, _, _, _, _, _, h => by
    obtain ⟨rfl, rfl, rfl⟩ := Proofs.Region.run_nil_inv (by simpa [expression] using h)
    exact ⟨rfl, rfl, by simp⟩
  | i :: is, _, _, _, _, _, _, hv, h => by
    obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.1 (hv i (by simp))
    have h' := Proofs.Region.run_val_inv hv' (by simpa [expression] using h)
    obtain ⟨rfl, rfl, rfl⟩ := run_consts (fun j hj => hv j (List.mem_cons_of_mem _ hj))
      (by simpa [expression] using h')
    exact ⟨rfl, rfl, by simp [hv']⟩


end Silmaril.Wasm.Cfg.Proofs.ExampleBrOut

namespace Silmaril.Wasm.Cfg.Proofs.ExampleBrOut

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Cfg.ExampleBrOut

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false


/-- **`body3` enters its block**: the state at the block's first segment, under its frame. -/
theorem enter3 (s : Store H) (f : Frame) :
    MStepC P host C body3 (initial body3 s f) ⟨.block ⟨[(0, 0)], 0⟩, [], [frame3], s, f⟩ := by
  have h := MStepC.enter (P := P) (host := host) (C := C) (body := body3) (b := ⟨[], 0⟩)
    (sg := ⟨[], some (.block .empty inner3)⟩) (stk := []) (stk₁ := []) (ws := []) (us := [])
    (ls := []) (s := s) (s₁ := s) (f := f) (f₁ := f) (a := 0) (c := inner3) (bt := .empty)
    (t₁ := []) (t₂ := []) (loop := false) (tryT := false) (cs := []) rfl rfl rfl .block
    (by simpa [expression] using (RunC.nil : RunC P host C s f [] [] s f (.normal [])))
    (by
      have := CondArm.plain (i := Instr.block .empty inner3) (ws := []) (us := []) (by simp)
      simpa using this) rfl rfl
  exact h

/-- A call-free region run to values is a Core run to them. -/
theorem core_of_run {s s' : Store H} {f f' : Frame} {code : List Admin} {vs : List Val}
    (h : Region.Run P host s f [] code s' f' (.normal vs)) :
    Steps P host ⟨s, f, code⟩ ⟨s', f', vals vs⟩ := by
  obtain ⟨c', hs, he⟩ := Region.run_sound h
  simp only [Region.Out.Ends] at he
  subst he
  simpa [vals] using hs

theorem val_i32 (k : BitVec 32) : (Admin.plain (.intConst .i32 k)).val? = some (.i32 k) := rfl

theorem fin_vals {s : Store H} {f : Frame} (vs : List Val) :
    Region.Run P host s f [] (vals vs ++ expression [] ++ []) s f (.normal vs) := by
  have h := Proofs.Region.run_vals (P := P) (host := host) (C := noCall) (s := s) (f := f)
    (vs := []) (ws := vs) (code := []) (o := .normal vs) (by simpa using
      (RunC.nil : RunC P host noCall s f vs [] s f (.normal vs)))
  simpa [expression] using h

/-- **`body0` returns `1` under its function label in Core 3.0.** -/
theorem core0 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 1 [] (expression body0)]⟩ ⟨s, f, vals [.i32 1]⟩ := by
  refine core_of_run (RunC.labelBr0 (us₁ := []) (us₂ := [.i32 1]) ?_ rfl (fin_vals _))
  exact .val (val_i32 1) .br

/-- **`body1` returns `7` under its function label** (the `br_if` is taken). -/
theorem core1 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 1 [] (expression body1)]⟩ ⟨s, f, vals [.i32 7]⟩ := by
  refine core_of_run (RunC.labelBr0 (us₁ := []) (us₂ := [.i32 7]) ?_ rfl (fin_vals _))
  exact .val (val_i32 7) (.val (val_i32 1) (.brIf (k := 1) (by
    simp only [show (1 : BitVec 32) ≠ 0 by decide, ↓reduceIte, List.singleton_append]
    exact RunC.br)))

/-- **`body4` returns `1, 2` under its function label.** -/
theorem core4 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 2 [] (expression body4)]⟩ ⟨s, f, vals [.i32 1, .i32 2]⟩ := by
  refine core_of_run (RunC.labelBr0 (us₁ := []) (us₂ := [.i32 1, .i32 2]) ?_ rfl (fin_vals _))
  exact .val (val_i32 1) (.val (val_i32 2) .br)

/-- **`body3` returns `5` under its function label** (the `br_table` leaves the block and the
function). -/
theorem core3 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 1 [] (expression body3)]⟩ ⟨s, f, vals [.i32 5]⟩ := by
  refine core_of_run (RunC.labelBr0 (us₁ := []) (us₂ := [.i32 5]) ?_ rfl (fin_vals _))
  have hbt : f.module.blockType? .empty = some ([], []) := rfl
  refine .block (ws := []) (us := []) hbt rfl ?_
  have hin : Region.Run P host s f [] (vals [] ++ expression inner3) s f (.br 1 [.i32 5]) :=
    .val (val_i32 5) (.val (val_i32 0) (.brData (ws := [.i32 5]) (us := [.i32 0]) (us' := [])
      (.tableLt (l := l1) rfl) (by simp only [List.append_nil]; exact RunC.br)))
  simpa using RunC.labelBrSucc (vs := []) (n := 0) (cont := []) (code := expression [.intConst .i32 0]) hin

/-- **`body2` returns `9` under its function label** (the `br_if` is not taken). -/
theorem core2 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 1 [] (expression body2)]⟩ ⟨s, f, vals [.i32 9]⟩ := by
  have hdrop : Steps P host ⟨s, f, vals [.i32 7] ++ [.plain .drop]⟩ ⟨s, f, vals []⟩ :=
    .single (Step.parametric (ParametricStep.drop (.i32 7)))
  have hin : Region.Run P host s f [] (expression body2) s f (.normal [.i32 9]) :=
    .val (val_i32 7) (.val (val_i32 0) (.brIf (k := 0) (by
      simp only [↓reduceIte, List.nil_append]
      exact .simple (by simp [SingleThreaded.Det.famOf]) hdrop
        (.val (val_i32 9) (by simpa using (RunC.nil : RunC P host noCall s f [.i32 9] [] s f _))))))
  exact core_of_run (RunC.labelNormal (vs := []) (by simpa using hin) (by simpa using
    (RunC.nil : RunC P host noCall s f [.i32 9] [] s f _)))

/-! ## The machine leaves the function at the branch (the fixed machine) -/

/-- **`body0`: the machine branches to the function label and reaches `exit` with `1`.** -/
theorem exit0 (s : Store H) (f : Frame) :
    MStepC P host C body0 (initial body0 s f) ⟨.exit, [.i32 1], [], s, f⟩ :=
  MStepC.brOut (sg := ⟨[.intConst .i32 1], some (.br l0)⟩) (ls := []) rfl rfl
    (.val (val_i32 1) .nil) rfl

/-- **`body1`: the taken `br_if` reaches `exit` with `7`.** -/
theorem exit1 (s : Store H) (f : Frame) :
    MStepC P host C body1 (initial body1 s f) ⟨.exit, [.i32 7], [], s, f⟩ :=
  MStepC.brIfOut (sg := ⟨[.intConst .i32 7, .intConst .i32 1], some (.brIf l0)⟩) (ls := [])
    (k := 1) rfl rfl (.val (val_i32 7) (.val (val_i32 1) .nil)) (by decide) rfl

/-- **`body3`: after entering its block, the `br_table` reaches `exit` with `5`.** -/
theorem exit3 (s : Store H) (f : Frame) :
    MStepC P host C body3 ⟨.block ⟨[(0, 0)], 0⟩, [], [frame3], s, f⟩ ⟨.exit, [.i32 5], [], s, f⟩ :=
  MStepC.brDataOut (sg := ⟨[.intConst .i32 5, .intConst .i32 0], some (.brTable [l1] l1)⟩)
    (ws := [.i32 5]) (us := [.i32 0]) (us' := []) (l := l1) rfl rfl
    (.val (val_i32 5) (.val (val_i32 0) .nil)) (.tableLt rfl) rfl

/-- **`body4`: the machine reaches `exit` with `1, 2`.** -/
theorem exit4 (s : Store H) (f : Frame) :
    MStepC P host C body4 (initial body4 s f) ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ :=
  MStepC.brOut (sg := ⟨[.intConst .i32 1, .intConst .i32 2], some (.br l0)⟩) (ls := []) rfl rfl
    (.val (val_i32 1) (.val (val_i32 2) .nil)) rfl

end Silmaril.Wasm.Cfg.Proofs.ExampleBrOut
