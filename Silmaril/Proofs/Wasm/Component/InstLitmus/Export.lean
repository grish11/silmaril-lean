module

public import Silmaril.Proofs.Wasm.Component.InstLitmus.Glob
public import Silmaril.Proofs.Wasm.Component.InstLitmus.Neg
public import Silmaril.Proofs.Wasm.Component.InstSem.Export
public import Silmaril.Proofs.Wasm.Component.InstEngine.Core3Det
public import Silmaril.Proofs.Wasm.Component.InstExport.Basic

/-!
# Instantiation litmus components: the export phase

* `globMod_play`, `globNode_play`: the module `globMod` and its node instantiate (the start
  function writes `42` into the global) and then answer `get()` with `42`, for every profile;
* `globMod_get_det`: at a deterministic profile, after a successful instantiation `get()` is
  answered `42` only (from the converse `core3_after_start_iff` and the uniqueness of normal
  forms);
* `globC_get`, `callGlobC_get`: the component plays, through `extI_inst_right` and
  `denI_of_denNodesI_fwd`;
* `trap1C_inst`: `[inst, fail ()]` is a play of `trap1C`;
* `trapC_denX`: at a deterministic profile the export phase of `trapC` never answers.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstLitmus

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Param Silmaril.Wasm.Component.InstLitmus
open Silmaril.Proofs.Wasm.Component.InstSem Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (liftMove)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

/-- Runs of an engine. -/
local notation "ESteps" => Silmaril.Wasm.Component.Engine.CoreEngine.Steps

theorem callee_getM {E : Engine} (a : E.FuncAddr) :
    callee? [a] globMod.exports getM = some (a, []) := rfl

section Pos

variable (P : Profile)

/-- **`globMod` instantiates, then answers `get()` with `42`.** -/
theorem globMod_play :
    roundsMoves [instRound (F := sigN 1) (X := sigN 0) [] .ready,
      exRound (R := Unit) (⟨getM, [], a42⟩ : Round (sigN 0) (sigN 1))] ∈
      (core3SemI P).sem globMod := by
  show _ ∈ engineStrategyI (core3P P) (instOfI (core3P P) globMod.mod globMod.imports
    globMod.exports) globMod.imports globMod.exports
  rw [instOfI_glob P]
  obtain ⟨_, -, hs⟩ := prepOk_eq globPrep_ok.1
  obtain ⟨t, hr, hf⟩ := glob_start (P := P) hs
  obtain ⟨t', hr', hf'⟩ := glob_get (P := P) hs
  have hp : [.inr (.ask getM), .inr (.ans getM a42)] ∈ engineStrategy (core3P P)
      ⟨globAfter (storeOf globPrep), [(1 : Nat)]⟩ globMod.imports globMod.exports := by
    refine Strategy.mem_ofLTS_of_mem_traces ⟨_, .vis ⟨_, rfl, ETrans.call (callee_getM _)⟩
      (.vis ⟨_, rfl, ETrans.oret hr' hf'⟩ (.nil _))⟩ ⟨_, .cons (.ask _) (.cons (.ret _ _) (.nil _))⟩
  have := engine_after_start (c' := (globAfter (storeOf globPrep), t)) (cs := [])
    (I := some (globI P)) (J := globI P) rfl rfl (.nil hr) hf hp
  exact this

/-- **The node of `globMod` instantiates, then answers `get()` with `42`.** -/
theorem globNode_play (e : Nat) :
    roundsMoves [instRound (F := sigU) (X := sigU) [] .ready,
      exRound (R := Unit) (⟨(0, .flat []), [], a42⟩ : Round sigU sigU)] ∈
      coreNodeI (core3SemI P) e globMod [] := by
  have hin := comp_rounds (σ := (core3SemI P).sem globMod)
    (τ := Strategy.ofHandler (liftH (widenH (CoreModule.exports globMod).length)))
    [([instRound (F := sigN 1) (X := sigN 0) [] .ready],
        (⟨none, [⟨none, InstAns.ready⟩], InstAns.ready⟩ : Round _ sigUI)),
      ([exRound (R := Unit) (⟨getM, [], a42⟩ : Round (sigN 0) (sigN 1))],
        (⟨some (0, .flat []), [⟨some getM, a42⟩], a42⟩ : Round _ sigUI))]
    (by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> rfl)
    (globMod_play P)
    (by
      refine mem_ofHandler_rounds _ fun u hu => ?_
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact .call (.pure _)
      · exact .call (.pure _))
  have hout := comp_rounds (σ := Strategy.ofHandler (implsN e [] (CoreModule.imports globMod).length))
    (τ := ((core3SemI P).sem globMod).comp
      (Strategy.ofHandler (liftH (widenH (CoreModule.exports globMod).length))))
    [([], (⟨none, [], InstAns.ready⟩ : Round _ sigUI)),
      ([], (⟨some (0, .flat []), [], a42⟩ : Round _ sigUI))]
    (by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> rfl)
    (Strategy.nil_mem _) hin
  exact hout

/-- The imports of a component without imports, ready at once. -/
theorem base0_rounds :
    roundsMoves [instRound (F := sigU) (X := sigU) [] .ready] ∈
      withReady (R := Unit) (Strategy.ofHandler (maskH 0)) := by
  simpa using withReady_maskH_rounds 0 [] (by simp)

/-- **(e)** -/
theorem globC_play :
    roundsMoves [instRound (F := sigU) (X := sigU) [] .ready,
      exRound (R := Unit) (⟨getQ, [], a42⟩ : Round sigU sigU)] ∈ globC.denI (core3SemI P) := by
  refine denI_of_denNodesI_fwd (core3SemI P) [] [.core globMod []] [getX 0] [] (r := 0) a42
    rfl (by decide) ?_
  simp only [denNodesI, Node.denI]
  have h := extI_inst_right (e := 0) (D := withReady (Strategy.ofHandler (maskH 0)))
    (N := coreNodeI (core3SemI P) 0 globMod []) [] [] [⟨(0, .flat []), [], a42⟩]
    (by simp) (by simpa using base0_rounds) (by simpa using globNode_play P 0)
  simpa [roundsMoves, allCalls, shiftRound, exRound] using h

/-- **(f)** -/
theorem callGlobC_play :
    roundsMoves [instRound (F := sigU) [⟨fQ 1, unitA⟩] .ready,
      exRound (R := Unit) (⟨getQ, [], a42⟩ : Round sigU sigU)] ∈
      callGlobC.denI (core3SemI P) := by
  refine denI_of_denNodesI_fwd (core3SemI P) hostI [.core (callMod 1) [Impl.fwd 0], .core globMod []]
    [getX 1] [⟨fQ 1, unitA⟩] (r := 1) a42 rfl (by decide) ?_
  simp only [denNodesI, Node.denI]
  have h₁ := extI_inst (e := hostI.length)
    (N := coreNodeI (core3SemI P) hostI.length (callMod 1) [Impl.fwd 0])
    [] [fR 1] [] InstAns.ready (by simpa using base_rounds [1])
    (by simpa [hostRound, Round.call] using
      (callNode_inst P callPrep_one hostI.length Nat.zero_lt_one)) (by simp)
  have h₂ := extI_inst_right (e := hostI.length + Node.width (Node.core (callMod 1) [Impl.fwd 0]))
    (D := extI hostI.length (withReady (Strategy.ofHandler (maskH hostI.length)))
      (coreNodeI (core3SemI P) hostI.length (callMod 1) [Impl.fwd 0]))
    (N := coreNodeI (core3SemI P) (hostI.length + Node.width (Node.core (callMod 1)
      [Impl.fwd 0])) globMod [])
    [⟨fQ 1, unitA⟩] [] [⟨(0, .flat []), [], a42⟩] (by simp)
    (by simpa [roundsMoves, allCalls, hostRound] using h₁)
    (by simpa using globNode_play P _)
  exact h₂

/-- **(g)** A trapping start function fails the instantiation of `trap1C`. -/
theorem trap1C_inst :
    (instRound (F := sigU) (X := sigU) [] (InstAns.fail ())).moves ∈ trap1C.denI (core3SemI P) := by
  refine denI_of_denNodesI _ _ _ _ _ _ ?_
  simp only [denNodesI, Node.denI]
  have hN : (instRound (F := sigU) (X := sigU) [] (InstAns.fail ())).moves ∈
      coreNodeI (core3SemI P) 0 trapMod [] := by
    have := coreNodeI_inst (core3SemI P) 0 trapMod [] [] (InstAns.fail ()) (trapMod_inst P)
      (by simp)
    simpa only [allCalls] using this
  have h₁ := extI_inst (e := 0) (N := coreNodeI (core3SemI P) 0 trapMod [])
    [] [] [] (InstAns.fail ()) (by simpa using base0_rounds) (by simpa using hN) (by simp)
  simpa [roundsMoves, allCalls] using h₁

end Pos

section Det

variable {o : GrowOracle}

/-- **At a deterministic profile, `get()` after a successful instantiation of `globMod` is
answered `42` only.** -/
theorem globMod_get_det {cs : List (Σ _ : (sigN 0).Op, Option Payload)} {r : Option Payload}
    (h : instPlay (F := sigN 1) cs .ready ++
        ([.inr (.ask getM), .inr (.ans getM r)] : List (Move (sigN 0) (sigN 1))).map liftMove ∈
      (core3SemI (profile o)).sem globMod) : r = a42 := by
  change _ ∈ engineStrategyI (core3P (profile o)) (instOfI (core3P (profile o)) globMod.mod
    globMod.imports globMod.exports) globMod.imports globMod.exports at h
  have hcs : cs = [] := by
    rcases cs with _ | ⟨⟨⟨⟨i, hi⟩, _⟩, _⟩, _⟩
    · rfl
    · exact absurd hi (Nat.not_lt_zero _)
  subst hcs
  obtain ⟨_, -, hs⟩ := prepOk_eq globPrep_ok.1
  obtain ⟨t, hr, hf⟩ := glob_start (P := profile o) hs
  obtain ⟨t', hr', hf'⟩ := glob_get (P := profile o) hs
  have hp := (core3_after_start_iff (I := instOfI (core3P (profile o)) globMod.mod globMod.imports
    globMod.exports) (J := globI (profile o)) (instOfI_glob _) rfl
    (c' := (globAfter (storeOf globPrep), t)) (.nil hr) hf _).1 h
  have htr := trace_of_mem_ofLTS (s := [.inr (.ask getM)]) hp trivial
  obtain ⟨z, hz⟩ := htr
  rcases run_cases hz with ⟨hl, -⟩ | ⟨y, ⟨m, hm, -⟩, -⟩ | ⟨o₁, l, y, hl, ⟨m, hm, hs₁⟩, hz₁⟩
  · cases hl
  · cases hm
  · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    cases hm
    cases hs₁ with
    | refuse hc =>
      have hcal : callee? (globI (profile o)).addrs globMod.exports getM = some ((1 : Nat), []) := rfl
      rw [hcal] at hc
      cases hc
    | call hc =>
      have hcal : callee? (globI (profile o)).addrs globMod.exports getM = some ((1 : Nat), []) := rfl
      rw [hcal] at hc
      cases hc
      rcases run_cases hz₁ with ⟨hl, -⟩ | ⟨y', ⟨m', hm', -⟩, -⟩ |
        ⟨o₂, l', y', hl', ⟨m', hm', hs₂⟩, -⟩
      · cases hl
      · cases hm'
      · obtain ⟨rfl, -⟩ := List.cons.inj hl'
        cases hm'
        cases hs₂ with
        | oret run final =>
          have he := Silmaril.Wasm.Game.reach_normal_unique run hr'
            (core3_noStep (.inr ⟨_, final⟩)) (core3_noStep (.inr ⟨_, hf'⟩))
          cases he
          rw [hf'] at final
          cases final
          rfl
        | otrap run final =>
          have he := Silmaril.Wasm.Game.reach_normal_unique run hr'
            (core3_noStep (.inr ⟨_, final⟩)) (core3_noStep (.inr ⟨_, hf'⟩))
          cases he
          rw [hf'] at final
          cases final

/-- **(c) The export phase of `trapC` never answers**, at a deterministic profile: its
instantiation never succeeds. -/
theorem trapC_denX : trapC.denX (core3SemI (profile o)) = ⊥ := by
  rw [Strategy.bot_eq_generate, Comp.denX, exportPhase]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  intro cs h
  have hr : ansInst .ready ∈ instPlay (F := sigU) cs (InstAns.ready (R := Unit)) ++
      p.map liftMove := by simp [instPlay]
  rcases trapC_moves h _ hr with h | h | h
  · cases h
  · cases h
  · exact h

end Det

end Silmaril.Proofs.Wasm.Component.InstLitmus
