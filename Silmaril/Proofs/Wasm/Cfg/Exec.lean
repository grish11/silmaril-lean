module

public import Silmaril.Wasm.Cfg.Exec.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Basic
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Execution.Core.Inversion.Thms

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.Exec

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (Det.famOf Det.Fam)

-- One tactic closes every rule of a family; on some rules some of its branches are unused.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

local macro "simple_res" : tactic => `(tactic| first
  | exact Or.inr rfl
  | (left; intro a ha; simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
     repeat' (rcases ha with rfl | ha)
     all_goals (try subst_vars)
     all_goals first
       | (left; simp [Silmaril.Wasm.SingleThreaded.Det.toAdmin_val?_ne_none, Admin.val?, constI32, aconst]; done)
       | (right; refine ⟨_, rfl, ?_⟩; simp [Det.famOf]; done)
       | (left; simp [Silmaril.Wasm.SingleThreaded.Det.toAdmin_val?_ne_none]; done)
       | (left; exact Silmaril.Wasm.SingleThreaded.Det.mem_vals ‹_›)
       | (left; obtain ⟨r, -, hr⟩ := List.mem_map.1 ‹_›; subst hr; simp [Admin.val?])))

theorem parametric_res {l is' : List Admin} (h : ParametricStep l is') : SimpleRes is' := by
  cases h <;> simple_res
theorem numeric_res {P} {l is' : List Admin} (h : NumericStep P l is') : SimpleRes is' := by
  cases h <;> simple_res
theorem vector_res {P} {l is' : List Admin} (h : VectorStep P l is') : SimpleRes is' := by
  cases h <;> simple_res
theorem variable_res {H} {c c' : Config H} (h : VariableStep c c') : SimpleRes c'.code := by
  cases h <;> simple_res
theorem table_res {H P} {c c' : Config H} (h : TableStep P c c') : SimpleRes c'.code := by
  cases h <;> simple_res
theorem memory_res {H P} {c c' : Config H} (h : MemoryStep P c c') : SimpleRes c'.code := by
  cases h <;> simple_res
theorem ref_res {H} {c c' : Config H} (h : RefStep c c') : SimpleRes c'.code := by
  cases h <;> simple_res
theorem aggregate_res {H} {c c' : Config H} (h : AggregateStep c c') : SimpleRes c'.code := by
  cases h <;> simple_res

/-! ## Lifting to `Step` -/

theorem val_none_of_noncontrol {a : Admin} (h : Det.famOf a ≠ .control) : a.val? = none := by
  cases a with
  | plain i => cases i <;> simp_all [Det.famOf, Admin.val?]
  | _ => simp_all [Det.famOf]

theorem stepRes_of {x : List Admin} (h : SimpleRes x) : StepRes x := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨[], by simp [h]⟩

theorem isCallRef_control {c : Admin} (h : c.IsCallRef) : Det.famOf c = .control := by
  cases c with
  | plain i => cases i <;> simp_all [Admin.IsCallRef, Det.famOf]
  | _ => simp_all [Admin.IsCallRef, Det.famOf]

theorem step_noncontrol {H P} {host : HostSemantics H} {c c' : Config H} (h : Step P host c c') :
    ∀ (us : List Val) (a : Admin), c.code = vals us ++ [a] → Det.famOf a ≠ .control →
      StepRes c'.code := by
  induction h with
  | parametric h => intro _ _ _ _; exact stepRes_of (Proofs.Exec.parametric_res h)
  | numeric h => intro _ _ _ _; exact stepRes_of (Proofs.Exec.numeric_res h)
  | vector h => intro _ _ _ _; exact stepRes_of (Proofs.Exec.vector_res h)
  | «variable» h => intro _ _ _ _; exact stepRes_of (Proofs.Exec.variable_res h)
  | table h => intro _ _ _ _; exact stepRes_of (Proofs.Exec.table_res h)
  | memory h => intro _ _ _ _; exact stepRes_of (Proofs.Exec.memory_res h)
  | reference h => intro _ _ _ _; exact stepRes_of (Proofs.Exec.ref_res h)
  | aggregate h => intro _ _ _ _; exact stepRes_of (Proofs.Exec.aggregate_res h)
  | @ctxtInstrs s s' f f' vs is is' rest hs hne ih =>
    intro us a hc hk
    have ha := val_none_of_noncontrol hk
    obtain ⟨vs₁, b, r, hb, rfl⟩ := Sim.exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs ++ vs₁) ++ b :: (r ++ rest) = vals us ++ a :: [] := by
      simp only at hc; rw [← hc]; simp
    obtain ⟨-, rfl, hr⟩ := Sim.vals_append_cons_inj hb ha hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hr
    rcases ih vs₁ b rfl hk with h | ⟨ws, hw⟩
    · left; intro x hx
      simp only [List.mem_append, List.append_nil] at hx
      rcases hx with hx | hx
      · exact Or.inl (Silmaril.Wasm.SingleThreaded.Det.mem_vals hx)
      · exact h x hx
    · right; exact ⟨vs ++ ws, by simp only at hw; simp [hw]⟩
  | @throwRefInstrs s f vs x rest hne =>
    intro us a hc hk
    have ha := val_none_of_noncontrol hk
    simp only [throwing] at hc
    have hc2 : vals (vs ++ [Val.ref (.exn x)]) ++ Admin.plain .throwRef :: rest = vals us ++ a :: [] := by
      rw [← hc]; simp [vals, Val.toAdmin]
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj (by simp [Admin.val?]) ha hc2
    simp [Det.famOf] at hk
  | _ =>
    intro us a hc hk
    have hl := congrArg List.getLast? hc
    simp at hl
    first
      | (simp [← hl, Det.famOf] at hk; done)
      | (simp [Det.famOf] at hk; done)
      | (subst hl; exact absurd (isCallRef_control ‹_›) hk)
      | (exfalso
         have ha := val_none_of_noncontrol hk
         simp only at hc
         rw [List.append_assoc, List.singleton_append] at hc
         obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj (by simp [Admin.val?]) ha hc
         simp [Det.famOf] at hk)

end Silmaril.Wasm.Cfg.Proofs.Exec

namespace Silmaril.Wasm.Cfg.Proofs.Exec

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SingleThreaded (Det.famOf Det.Fam)

/-! ## Simple code followed by anything (milestone 2c) -/

theorem simpleAdmin_nonval {a : Admin} (h : SimpleAdmin a) (hv : a.val? = none) :
    Det.famOf a ≠ .control := by
  rcases h with h | ⟨i, rfl, hk⟩
  · exact absurd hv h
  · exact hk

/-- A step of `val* a A' ++ R`, with `a` non-control, leaves simple code before `A' ++ R`, or a
trap after values. -/
theorem simple_step {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') {vs : List Val} {a : Admin} {A' R : List Admin}
    (hk : Det.famOf a ≠ .control) (hc : c.code = vals vs ++ a :: (A' ++ R)) :
    (∃ B, (∀ b ∈ B, SimpleAdmin b) ∧ c'.code = B ++ (A' ++ R)) ∨
      (∃ ws, c'.code = vals ws ++ [.trap] ++ (A' ++ R)) := by
  have ha := val_none_of_noncontrol hk
  rcases c with ⟨s, f, code⟩
  rcases c' with ⟨s', f', code'⟩
  simp only at hc
  subst hc
  rcases Sim.Step.split_head ha h with ⟨ws, us, is', rfl, hst, he⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · simp only at he ⊢
    rcases step_noncontrol hst us a rfl hk with hall | ⟨ws', rfl⟩
    · left
      refine ⟨vals ws ++ is', ?_, by rw [he]⟩
      intro b hb
      rcases List.mem_append.1 hb with hb | hb
      · exact Or.inl (Silmaril.Wasm.SingleThreaded.Det.mem_vals hb)
      · exact hall b hb
    · right; exact ⟨ws ++ ws', by rw [he]; simp⟩
  · simp [Det.famOf] at hk
  · simp [Det.famOf] at hk

/-- A list of simple administrative instructions is all values, or has a first non-value, which
is a non-control instruction. -/
theorem simple_split {B : List Admin} (hB : ∀ b ∈ B, SimpleAdmin b) :
    (∃ vs, B = vals vs) ∨ ∃ vs a A', B = vals vs ++ a :: A' ∧ Det.famOf a ≠ .control ∧
      ∀ b ∈ A', SimpleAdmin b := by
  by_cases hall : B.all Admin.isVal = true
  · left
    refine ⟨B.filterMap Admin.val?, Silmaril.Wasm.SingleThreaded.Det.eq_vals_of_all ?_⟩
    intro x hx
    have := List.all_eq_true.1 hall x hx
    simpa [Admin.isVal, Option.isSome_iff_ne_none] using this
  · right
    obtain ⟨vs, a, A', ha, rfl⟩ := Sim.exists_head_of_not_all (by simpa using hall)
    exact ⟨vs, a, A', rfl, simpleAdmin_nonval (hB a (by simp)) ha,
      fun b hb => hB b (by simp [hb])⟩

/-- At position `j`, a step of a non-control instruction stays mid-instruction or exits by trap. -/
theorem resid_at_step {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {c c' : Config H} (h : Step P host c c') {is : List Instr} {j : Nat} {i : Instr}
    (hi : is[j]? = some i) (hk : Det.famOf (.plain i) ≠ .control) (hr : Resid is (.at j) c.code) :
    Resid is (.mid j) c'.code ∨ Resid is .exiting c'.code := by
  generalize hcode : c.code = code at hr
  cases hr with
  | «at» vs hj =>
    have hjl : j < is.length := by
      rcases Nat.lt_or_ge j is.length with h' | h'
      · exact h'
      · simp [List.getElem?_eq_none h'] at hi
    have hd : is.drop j = i :: is.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hjl]; simp [List.getElem?_eq_getElem hjl] at hi; rw [hi]
    have hc : c.code = vals vs ++ Admin.plain i :: ([] ++ expression (is.drop (j + 1))) := by
      rw [hcode, hd]; simp [expression]
    rcases simple_step h hk hc with ⟨B, hB, he⟩ | ⟨ws, he⟩
    · left; rw [he]; simpa using Resid.mid B hB hjl
    · right; rw [he]; exact Resid.exiting (is := is) ws .trap

/-- Mid-instruction, either only values are left (so the position is the next instruction), or a
step stays mid-instruction or exits by trap. -/
theorem resid_mid_step {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
    {is : List Instr} {j : Nat} {code : List Admin} (hr : Resid is (.mid j) code) :
    Resid is (.at (j + 1)) code ∨
      ∀ {c c' : Config H}, c.code = code → Step P host c c' →
        Resid is (.mid j) c'.code ∨ Resid is .exiting c'.code := by
  cases hr with
  | mid B hB hj =>
    rcases simple_split hB with ⟨vs, rfl⟩ | ⟨vs, a, A', rfl, hk, hA'⟩
    · left; exact Resid.at vs hj
    · right
      intro c c' hc h
      have hc' : c.code = vals vs ++ a :: (A' ++ expression (is.drop (j + 1))) := by
        rw [hc]; simp
      rcases simple_step h hk hc' with ⟨B', hB', he⟩ | ⟨ws, he⟩
      · left
        rw [he, ← List.append_assoc]
        exact Resid.mid (B' ++ A') (fun b hb => (List.mem_append.1 hb).elim (hB' b) (hA' b)) hj
      · right; rw [he]; exact Resid.exiting ws .trap

end Silmaril.Wasm.Cfg.Proofs.Exec

namespace Silmaril.Wasm.Cfg.Proofs.Exec

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Execution.Core

/-! ## Entering structured instructions (milestone 3a) -/

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

theorem drop_cons {is : List Instr} {j : Nat} {i : Instr} (hi : is[j]? = some i) :
    expression (is.drop j) = .plain i :: expression (is.drop (j + 1)) := by
  have hjl : j < is.length := by
    rcases Nat.lt_or_ge j is.length with h' | h'
    · exact h'
    · simp [List.getElem?_eq_none h'] at hi
  rw [List.drop_eq_getElem_cons hjl]
  simp [List.getElem?_eq_getElem hjl] at hi
  simp [expression, hi]

/-- A step of `val* i rest`, `i` a structured instruction, is a step of `val* i` in context. -/
theorem head_of {s s' : Store H} {f f' : Frame} {vs : List Val} {i : Instr} {es es' : List Admin}
    (hv : (Admin.plain i).val? = none) (hi : i ≠ .throwRef)
    (h : Step P host ⟨s, f, vals vs ++ .plain i :: es⟩ ⟨s', f', es'⟩) :
    ∃ ws us is', vs = ws ++ us ∧ Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s', f', is'⟩ ∧
      es' = vals ws ++ is' ++ es := by
  rcases Sim.Step.split_head hv h with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact h
  · cases h
  · simp only [Admin.plain.injEq] at h; exact absurd h hi

/-- Resolve a step at position `j` whose instruction is `i` to a step of `val* i`. -/
theorem at_head {c c' : Config H} (h : Step P host c c') {is : List Instr} {j : Nat} {i : Instr}
    (hi : is[j]? = some i) (hv : (Admin.plain i).val? = none) (hne : i ≠ .throwRef)
    (hr : Resid is (.at j) c.code) :
    ∃ vs ws us is', vs = ws ++ us ∧ Step P host ⟨c.store, c.frame, vals us ++ [.plain i]⟩
      ⟨c'.store, c'.frame, is'⟩ ∧ c'.code = vals ws ++ is' ++ expression (is.drop (j + 1)) := by
  generalize hcode : c.code = code at hr
  cases hr with
  | «at» vs hj =>
    rcases c with ⟨s, f, cc⟩
    rcases c' with ⟨s', f', cc'⟩
    dsimp only at hcode ⊢
    subst hcode
    rw [drop_cons hi] at h
    obtain ⟨ws, us, is', rfl, hs, rfl⟩ := head_of hv hne h
    exact ⟨_, ws, us, is', rfl, hs, rfl⟩

theorem resid_at_block_step {c c' : Config H} (h : Step P host c c') {is b : List Instr}
    {j : Nat} {bt : BlockType} (hi : is[j]? = some (.block bt b)) (hr : Resid is (.at j) c.code) :
    Resid is (.inArm j 0 (.at 0)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame := by
  obtain ⟨-, ws, us, is', -, hs, hc⟩ := at_head h hi rfl (by simp) hr
  obtain ⟨ws', vs, t₁, t₂, rfl, -, -, he⟩ := Step.block_vals_inv hs
  simp only [Config.mk.injEq] at he
  obtain ⟨hs', hf', rfl⟩ := he
  refine ⟨?_, hs', hf'⟩
  rw [hc]
  have := Resid.inBlock (ws ++ ws') t₂.length hi (Resid.at (is := b) (j := 0) vs (Nat.zero_le _))
  simpa using this

theorem resid_at_loop_step {c c' : Config H} (h : Step P host c c') {is b : List Instr}
    {j : Nat} {bt : BlockType} (hi : is[j]? = some (.loop bt b)) (hr : Resid is (.at j) c.code) :
    Resid is (.inArm j 0 (.at 0)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame := by
  obtain ⟨-, ws, us, is', -, hs, hc⟩ := at_head h hi rfl (by simp) hr
  obtain ⟨ws', vs, t₁, t₂, rfl, -, -, he⟩ := Step.loop_vals_inv hs
  simp only [Config.mk.injEq] at he
  obtain ⟨hs', hf', rfl⟩ := he
  refine ⟨?_, hs', hf'⟩
  rw [hc]
  have := Resid.inLoop (ws ++ ws') t₁.length hi (Resid.at (is := b) (j := 0) vs (Nat.zero_le _))
  simpa using this

theorem resid_at_tryTable_step {c c' : Config H} (h : Step P host c c') {is b : List Instr}
    {j : Nat} {bt : BlockType} {cs : List Catch} (hi : is[j]? = some (.tryTable bt cs b))
    (hr : Resid is (.at j) c.code) :
    Resid is (.inArm j 0 (.at 0)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame := by
  obtain ⟨-, ws, us, is', -, hs, hc⟩ := at_head h hi rfl (by simp) hr
  obtain ⟨ws', vs, t₁, t₂, rfl, -, -, he⟩ := Step.tryTable_vals_inv hs
  simp only [Config.mk.injEq] at he
  obtain ⟨hs', hf', rfl⟩ := he
  refine ⟨?_, hs', hf'⟩
  rw [hc]
  have := Resid.inTry (ws ++ ws') t₂.length t₂.length hi
    (Resid.at (is := b) (j := 0) vs (Nat.zero_le _))
  simpa using this

theorem resid_at_if_step {c c' : Config H} (h : Step P host c c') {is t e : List Instr}
    {j : Nat} {bt : BlockType} (hi : is[j]? = some (.if_ bt t e)) (hr : Resid is (.at j) c.code) :
    ∃ a, Resid is (.ifArm j a) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame := by
  obtain ⟨-, ws, us, is', -, hs, hc⟩ := at_head h hi rfl (by simp) hr
  obtain ⟨ws', k, rfl, he⟩ := Step.if_vals_inv hs
  simp only [Config.mk.injEq] at he
  obtain ⟨hs', hf', rfl⟩ := he
  refine ⟨if k = 0 then 1 else 0, ?_, hs', hf'⟩
  rw [hc]
  split_ifs
  · simpa using Resid.ifArm (ws ++ ws') hi (a := 1) (c := e) rfl
  · simpa using Resid.ifArm (ws ++ ws') hi (a := 0) (c := t) rfl

theorem resid_ifArm_step {c c' : Config H} (h : Step P host c c') {is : List Instr} {k a : Nat}
    (hr : Resid is (.ifArm k a) c.code) :
    Resid is (.inArm k a (.at 0)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame := by
  generalize hcode : c.code = code at hr
  cases hr with
  | @ifArm _ cc t e _ _ bt vs hk ha =>
    rcases c with ⟨s, f, x⟩
    rcases c' with ⟨s', f', x'⟩
    dsimp only at hcode ⊢
    subst hcode
    rw [List.append_assoc, List.singleton_append] at h
    obtain ⟨ws, us, is', rfl, hs, rfl⟩ := head_of rfl (by simp) h
    obtain ⟨ws', vs, t₁, t₂, rfl, -, -, he⟩ := Step.block_vals_inv hs
    simp only [Config.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    refine ⟨?_, rfl, rfl⟩
    have := Resid.inIf (ws ++ ws') t₂.length hk ha (Resid.at (is := cc) (j := 0) vs (Nat.zero_le _))
    simpa using this

/-- Leaving a `LABEL` whose body is only values (`label-vals`, under the sequence context). -/
theorem label_vals_step {c c' : Config H} (h : Step P host c c') {vs ws : List Val} {n : Nat}
    {cont : List Instr} {rest : List Admin}
    (hc : c.code = vals vs ++ [.label n cont (vals ws)] ++ rest) :
    c' = ⟨c.store, c.frame, vals (vs ++ ws) ++ rest⟩ := by
  rcases c with ⟨s, f, x⟩
  dsimp only at hc
  subst hc
  rw [List.append_assoc, List.singleton_append] at h
  obtain ⟨c₀, h₀, rfl⟩ := Step.ctx_in_seq (by simp [Admin.IsCtx]) h
  rcases Step.label_inv h₀ with ⟨_, _, _, hs, -⟩ | ⟨out, hx, rfl⟩
  · exact (Step.not_vals hs).elim
  · rw [labelExit_of_vals hx]; simp

/-- **Falling out of a block, loop or `if` arm**: when the arm has run to its end, the next step
leaves the label with its values, at the instruction after the structured one. -/
theorem resid_inArm_done_step {c c' : Config H} (h : Step P host c c') {is : List Instr}
    {k a m : Nat} (hlen : ∀ i b, is[k]? = some i → armOf i a = some b → m = b.length)
    (hnt : ∀ bt cs b, is[k]? ≠ some (.tryTable bt cs b))
    (hr : Resid is (.inArm k a (.at m)) c.code) :
    Resid is (.at (k + 1)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame := by
  have hkl : ∀ {i}, is[k]? = some i → k + 1 ≤ is.length := fun {i} hk => by
    rcases Nat.lt_or_ge k is.length with h' | h'
    · omega
    · simp [List.getElem?_eq_none h'] at hk
  have fin : ∀ {vs ws : List Val} {n : Nat} {cont : List Instr},
      k + 1 ≤ is.length →
      c.code = vals vs ++ [.label n cont (vals ws)] ++ expression (is.drop (k + 1)) →
      Resid is (.at (k + 1)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame := by
    intro vs ws n cont hk hc
    rw [label_vals_step h hc]
    exact ⟨Resid.at _ hk, rfl, rfl⟩
  generalize hcode : c.code = code at hr
  cases hr with
  | @inBlock _ b _ _ _ inner vs n hk hin =>
    have hm := hlen _ b hk rfl
    generalize hl : Loc.at m = l at hin
    cases hin with
    | «at» ws _ =>
      cases hl; subst hm
      exact fin (vs := vs) (ws := ws) (n := n) (cont := []) (hkl hk) (by rw [hcode]; simp [expression])
    | _ => cases hl
  | @inLoop _ b _ bt _ inner vs n hk hin =>
    have hm := hlen _ b hk rfl
    generalize hl : Loc.at m = l at hin
    cases hin with
    | «at» ws _ =>
      cases hl; subst hm
      exact fin (vs := vs) (ws := ws) (n := n) (cont := [.loop bt b]) (hkl hk) (by rw [hcode]; simp [expression])
    | _ => cases hl
  | @inIf _ cc t e _ _ _ _ inner vs n hk ha hin =>
    have hm := hlen _ cc hk ha
    generalize hl : Loc.at m = l at hin
    cases hin with
    | «at» ws _ =>
      cases hl; subst hm
      exact fin (vs := vs) (ws := ws) (n := n) (cont := []) (hkl hk) (by rw [hcode]; simp [expression])
    | _ => cases hl
  | inTry _ _ _ hk _ => exact (hnt _ _ _ hk).elim

end Silmaril.Wasm.Cfg.Proofs.Exec
