module

public import Silmaril.Wasm.Logic.Modal.TwoDrop.Defs
public import Silmaril.Wasm.Binaryen.SimplifyLocalsLiteMacro
public import Silmaril.Wasm.Execution.Core.Properties
import Lean.Elab.Tactic.Omega

import Lean

@[expose] public section
namespace Silmaril.Logic.Modal.Wasm.TwoDrop
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Logic.Reachability.Wasm (start middle finish)

variable {H : Type} (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame)
    (vs : List Val) (a b : Val)

/-- Invert every actual successor, including reductions admitted through contexts. -/
theorem start_successor_iff (d : Config H) :
    Step P host (start s f vs a b) d ↔ d = middle s f vs a := by
  constructor
  · intro h
    have unique := Silmaril.Wasm.Binaryen.SimplifyLocalsLite.drop_step_unique
      (vs := vs ++ [a]) (v := b) (rest := [.plain .drop])
      (by simpa [start, vals, List.append_assoc] using h)
    simpa [middle, vals, List.append_assoc] using unique
  · rintro rfl
    exact Reachability.Wasm.first_step P host s f vs a b

/-- The second DROP also has exactly the displayed successor. -/
theorem middle_successor_iff (d : Config H) :
    Step P host (middle s f vs a) d ↔ d = finish s f vs := by
  constructor
  · intro h
    have unique := Silmaril.Wasm.Binaryen.SimplifyLocalsLite.drop_step_unique
      (vs := vs) (v := a) (rest := []) (by simpa [middle] using h)
    simpa [finish] using unique
  · rintro rfl
    exact Reachability.Wasm.second_step P host s f vs a

/-- Native returned values have no one-step successors. -/
theorem finish_deadlock (d : Config H) : ¬ Step P host (finish s f vs) d :=
  Step.not_vals

theorem finish_terminal : (finish s f vs).Terminal := ⟨.values vs, rfl⟩

/-- The first box is proved from successor inversion, not merely an exhibited trace. -/
theorem start_box_middle :
    Sat (observations P host s f vs a b) (.box (.atom .middle)) := by
  intro d hd
  exact (start_successor_iff P host s f vs a b d).mp hd

/-- Every two-step execution reaches the exact native final configuration. -/
theorem start_box_box_finish :
    Sat (observations P host s f vs a b) (.box (.box (.atom .finish))) := by
  intro d hd e he
  have hm := (start_successor_iff P host s f vs a b d).mp hd
  subst d
  exact (middle_successor_iff P host s f vs a e).mp he

/-- Actual terminality, rather than a proposition defined by modal translation. -/
theorem start_diamond_diamond_terminal :
    Sat (observations P host s f vs a b) (diamond (diamond (.atom .terminal))) := by
  apply (diamond_iff _ _ _).mpr
  refine ⟨middle s f vs a, Reachability.Wasm.first_step P host s f vs a b, ?_⟩
  apply (diamond_iff _ _ _).mpr
  exact ⟨finish s f vs, Reachability.Wasm.second_step P host s f vs a,
    finish_terminal s f vs⟩

/-- The live initial configuration is distinct from its immediate successor. -/
theorem start_ne_middle : start s f vs a b ≠ middle s f vs a := by
  intro same
  have lengths := congrArg (fun c : Config H => c.code.length) same
  simp only [start, middle, List.length_append, List.length_cons, List.length_nil] at lengths
  omega

/-- At a live state, □middle holds while middle itself fails. -/
theorem start_not_middle : ¬ Sat (observations P host s f vs a b) (.atom .middle) :=
  start_ne_middle s f vs a b

theorem live_T_counterexample :
    ¬ Sat (observations P host s f vs a b) (.imp (.box (.atom .middle)) (.atom .middle)) := by
  intro hT
  exact start_not_middle P host s f vs a b (hT (start_box_middle P host s f vs a b))

/-- No reflexive edge is silently added to actual execution. -/
theorem start_not_self_step : ¬ Step P host (start s f vs a b) (start s f vs a b) := by
  intro h
  exact start_ne_middle s f vs a b ((start_successor_iff P host s f vs a b _).mp h)

/-- Box bottom is intentionally true at an actual deadlock. -/
theorem finish_box_bottom :
    Holds (observations P host s f vs a b) (.box (.bot : Modal.Formula signature)) (finish s f vs) := by
  intro d hd
  exact (finish_deadlock P host s f vs d hd).elim

/-- Deadlock vacuity supplies a second, independent failure of T. -/
theorem deadlock_T_counterexample :
    ¬ Holds (observations P host s f vs a b) (.imp (.box .bot) .bot) (finish s f vs) := by
  intro hT
  exact hT (finish_box_bottom P host s f vs a b)

/-- The all-successor client reaches the existing normal K semantics. -/
theorem modal_start_box_box_finish :
    Modal.Sat (toModal (observations P host s f vs a b)) (.box (.box (.atom .finish))) :=
  (sat_toModal _ _).mp (start_box_box_finish P host s f vs a b)

theorem modal_live_T_counterexample :
    ¬ Modal.Sat (toModal (observations P host s f vs a b))
      (.imp (.box (.atom .middle)) (.atom .middle)) := by
  intro h
  exact live_T_counterexample P host s f vs a b ((sat_toModal _ _).mpr h)

/- Dependency ceilings reject incomplete proofs or additional assumptions. -/
run_elab do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``start_successor_iff, ``middle_successor_iff, ``finish_deadlock, ``start_box_middle, ``start_box_box_finish, ``start_diamond_diamond_terminal, ``start_not_self_step, ``live_T_counterexample, ``finish_box_bottom, ``deadlock_T_counterexample, ``modal_start_box_box_finish, ``modal_live_T_counterexample] do
    for axiomName in (← Lean.collectAxioms name) do
      unless permitted.contains axiomName do
        throwError "Unexpected axiom in Wasm modal observations"

end Silmaril.Logic.Modal.Wasm.TwoDrop
