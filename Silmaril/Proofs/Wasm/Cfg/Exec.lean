module

public import Silmaril.Wasm.Cfg.Exec.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Basic
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.Execution.Core.Properties

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
