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
