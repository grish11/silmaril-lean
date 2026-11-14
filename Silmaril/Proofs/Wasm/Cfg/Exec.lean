module

public import Silmaril.Wasm.Cfg.Exec.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Basic

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

end Silmaril.Wasm.Cfg.Proofs.Exec
