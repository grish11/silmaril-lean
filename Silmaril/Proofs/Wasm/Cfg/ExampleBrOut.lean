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

/-- The branch instructions: `br`, `br_if` and the data-dependent branches. -/
def IsBranch (T : Instr) : Prop := (∃ l, T = .br l) ∨ (∃ l, T = .brIf l) ∨ T.IsBrData

/-- **A branch only falls through or branches**, in a one-instruction region run. -/
theorem branch_run_inv {s s' : Store H} {f f' : Frame} {W : List Val} {T : Instr}
    {o : Region.Out} (hT : IsBranch T) (h : RunC P host C s f W [.plain T] s' f' o) :
    (∃ us, o = .normal us) ∨ ∃ l us, o = .br l us := by
  rcases hT with ⟨l, rfl⟩ | ⟨l, rfl⟩ | hd
  · obtain ⟨rfl, -, -⟩ := Proofs.Region.run_br_inv h; exact .inr ⟨_, _, rfl⟩
  · cases h with
    | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
    | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
    | val hv => simp [Admin.val?] at hv
    | simple hi => simp [SingleThreaded.Det.famOf] at hi
    | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi
    | brData hb => cases hb
    | @brIf _ _ _ _ _ k _ _ _ h' =>
      by_cases hk : k = 0
      · simp only [hk, ↓reduceIte, List.nil_append] at h'
        obtain ⟨rfl, -, -⟩ := Proofs.Region.run_nil_inv h'; exact .inl ⟨_, rfl⟩
      · simp only [hk, ↓reduceIte, List.singleton_append] at h'
        obtain ⟨rfl, -, -⟩ := Proofs.Region.run_br_inv h'; exact .inr ⟨_, _, rfl⟩
  · cases T <;> simp only [Instr.IsBrData] at hd <;>
    (cases h with
      | brData hb h' =>
        cases hb <;> simp only [List.append_nil] at h' <;>
          first
            | (obtain ⟨rfl, -, -⟩ := Proofs.Region.run_nil_inv h'; exact .inl ⟨_, rfl⟩)
            | (obtain ⟨rfl, -, -⟩ := Proofs.Region.run_br_inv h'; exact .inr ⟨_, _, rfl⟩)
      | returnCallRef hc => simp [Admin.IsReturnCallRef] at hc
      | returnCallRefNull hc => simp [Admin.IsReturnCallRef] at hc
      | val hv => simp [Admin.val?] at hv
      | simple hi => simp [SingleThreaded.Det.famOf] at hi
      | simpleTrap hi => simp [SingleThreaded.Det.famOf] at hi)

/-- **The machine is stuck at a block of constants whose terminator branches to the function
label**: every label the terminator can branch to has no frame. -/
theorem stuck_brOut {body : Expr} {b : BlockId} {sg : Segment} {stk : List Val}
    {ls : List LFrame} {s : Store H} {f : Frame} {st' : MState H} {T : Instr}
    (hb : lookup body b = some sg) (hv : ∀ i ∈ sg.body, (Admin.plain i).val? ≠ none)
    (hterm : sg.term = some T) (hT : IsBranch T)
    (hbr : ∀ l, T = .br l → ls[l.toNat]? = none)
    (hbrIf : ∀ l, T = .brIf l → ls[l.toNat]? = none ∧
      ∀ W, stk ++ sg.body.filterMap (fun i => (Admin.plain i).val?) ≠ W ++ [.i32 0])
    (hdata : ∀ us us' X W, stk ++ sg.body.filterMap (fun i => (Admin.plain i).val?) = W ++ us →
      BrStep s f us T us' X → ∃ l, X = [.plain (.br l)] ∧ ls[l.toNat]? = none) :
    ¬ MStepC P host C body ⟨.block b, stk, ls, s, f⟩ st' := by
  intro h
  cases h with
  | fall hb' ht => rw [hb] at hb'; cases hb'; simp_all
  | br hb' ht _ hL =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht; simp_all
  | brIfTaken hb' ht _ _ hL =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht; simp_all
  | brIfNot hb' ht hr =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    obtain ⟨rfl, rfl, ho⟩ := run_consts hv hr
    simp only [Region.Out.normal.injEq] at ho
    exact (hbrIf _ rfl).2 _ ho.symm
  | brDataTaken hb' ht hr hbs hL =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    obtain ⟨rfl, rfl, ho⟩ := run_consts hv hr
    simp only [Region.Out.normal.injEq] at ho
    obtain ⟨l', hX, hl'⟩ := hdata _ _ _ _ ho.symm hbs
    simp only [List.cons.injEq, Admin.plain.injEq, Instr.br.injEq, and_true] at hX
    subst hX; simp_all
  | brDataNot hb' ht hr hbs =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    obtain ⟨rfl, rfl, ho⟩ := run_consts hv hr
    simp only [Region.Out.normal.injEq] at ho
    obtain ⟨l', hX, -⟩ := hdata _ _ _ _ ho.symm hbs
    cases hX
  | enter hb' ht _ hkind =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    rcases hT with ⟨l, rfl⟩ | ⟨l, rfl⟩ | hd <;> cases hkind <;> simp_all [Instr.IsBrData]
  | ret hb' ht =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    rcases hT with ⟨l, h⟩ | ⟨l, h⟩ | hd <;> simp_all [Instr.IsBrData]
  | trap hb' ht =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    rcases hT with ⟨l, h⟩ | ⟨l, h⟩ | hd <;> simp_all [Instr.IsBrData]
  | termTrap hb' ht _ hth =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    rcases branch_run_inv hT hth with ⟨us, h⟩ | ⟨l, us, h⟩ <;> cases h
  | bodyTrap hb' hr =>
    rw [hb] at hb'; cases hb'
    obtain ⟨-, -, ho⟩ := run_consts hv hr; cases ho
  | raise hb' ht hi =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    rcases hT with ⟨l, rfl⟩ | ⟨l, rfl⟩ | hd
    · simp [Instr.IsThrow] at hi
    · simp [Instr.IsThrow] at hi
    · cases T <;> simp only [Instr.IsThrow, Instr.IsBrData] at hi hd
  | catch_ hb' ht hi =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    rcases hT with ⟨l, rfl⟩ | ⟨l, rfl⟩ | hd
    · simp [Instr.IsThrow] at hi
    · simp [Instr.IsThrow] at hi
    · cases T <;> simp only [Instr.IsThrow, Instr.IsBrData] at hi hd
  | bodyRaise hb' hr =>
    rw [hb] at hb'; cases hb'
    obtain ⟨-, -, ho⟩ := run_consts hv hr; cases ho
  | bodyCatch hb' hr =>
    rw [hb] at hb'; cases hb'
    obtain ⟨-, -, ho⟩ := run_consts hv hr; cases ho
  | tailNull hb' ht hi =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    rcases hT with ⟨l, rfl⟩ | ⟨l, rfl⟩ | hd
    · simp [Instr.IsTailCall] at hi
    · simp [Instr.IsTailCall] at hi
    · cases T <;> simp only [Instr.IsTailCall, Instr.IsBrData] at hi hd
  | tail hb' ht hi =>
    rw [hb] at hb'; cases hb'; rw [hterm] at ht; cases ht
    rcases hT with ⟨l, rfl⟩ | ⟨l, rfl⟩ | hd
    · simp [Instr.IsTailCall] at hi
    · simp [Instr.IsTailCall] at hi
    · cases T <;> simp only [Instr.IsTailCall, Instr.IsBrData] at hi hd

end Silmaril.Wasm.Cfg.Proofs.ExampleBrOut

namespace Silmaril.Wasm.Cfg.Proofs.ExampleBrOut

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Cfg.ExampleBrOut

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false


/-- A stuck start that is not a sink reaches no sink. -/
theorem no_sink_of_stuck {body : Expr} {st₀ : MState H}
    (hst : ∀ st', ¬ MStepC P host C body st₀ st') (hs : ¬ st₀.node.IsSink) :
    ∀ st', Relation.ReflTransGen (MStepC P host C body) st₀ st' → ¬ st'.node.IsSink := by
  intro st' h
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨st₁, h1, -⟩
  · exact hs
  · exact absurd h1 (hst _)

theorem stuck0 (s : Store H) (f : Frame) (st' : MState H) :
    ¬ MStepC P host C body0 (initial body0 s f) st' :=
  stuck_brOut (sg := ⟨[.intConst .i32 1], some (.br l0)⟩) (T := .br l0) rfl
    (by simp [Admin.val?]) rfl (.inl ⟨_, rfl⟩) (fun _ _ => rfl)
    (fun _ h => by cases h) (fun _ _ _ _ _ h => by cases h)

theorem stuck1 (s : Store H) (f : Frame) (st' : MState H) :
    ¬ MStepC P host C body1 (initial body1 s f) st' :=
  stuck_brOut (sg := ⟨[.intConst .i32 7, .intConst .i32 1], some (.brIf l0)⟩) (T := .brIf l0) rfl
    (by simp [Admin.val?]) rfl (.inr (.inl ⟨_, rfl⟩)) (fun _ h => by cases h)
    (fun _ h => by
      cases h
      refine ⟨rfl, fun W hW => ?_⟩
      have := congrArg List.getLast? hW
      simp [Admin.val?, Val.i32] at this
      exact absurd this (by decide))
    (fun _ _ _ _ _ h => by cases h)

theorem stuck4 (s : Store H) (f : Frame) (st' : MState H) :
    ¬ MStepC P host C body4 (initial body4 s f) st' :=
  stuck_brOut (sg := ⟨[.intConst .i32 1, .intConst .i32 2], some (.br l0)⟩) (T := .br l0) rfl
    (by simp [Admin.val?]) rfl (.inl ⟨_, rfl⟩) (fun _ _ => rfl)
    (fun _ h => by cases h) (fun _ _ _ _ _ h => by cases h)

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

theorem stuck3 (s : Store H) (f : Frame) (st' : MState H) :
    ¬ MStepC P host C body3 ⟨.block ⟨[(0, 0)], 0⟩, [], [frame3], s, f⟩ st' :=
  stuck_brOut (sg := ⟨[.intConst .i32 5, .intConst .i32 0], some (.brTable [l1] l1)⟩)
    (T := .brTable [l1] l1) rfl (by simp [Admin.val?]) rfl (.inr (.inr trivial))
    (fun _ h => by cases h) (fun _ h => by cases h)
    (fun us us' X W _ hbs => by
      cases hbs with
      | tableLt hl =>
        have hm := List.mem_of_getElem? hl
        simp only [List.mem_singleton] at hm
        subst hm
        exact ⟨_, rfl, rfl⟩
      | tableGe => exact ⟨_, rfl, rfl⟩)

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

theorem initial_not_sink (body : Expr) (b : BlockId) (h : cfgEntry body = .block b) (s : Store H)
    (f : Frame) : ¬ (initial body s f).node.IsSink := by
  simp [initial, h, Target.IsSink]

end Silmaril.Wasm.Cfg.Proofs.ExampleBrOut
