module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Defs
import Mathlib.Data.List.Perm.Basic
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra widths : List Width} {saved carried result w : Width}

theorem Slots.find?_origin {slots : Slots widths} {origin : Nat} {ref : Var widths w}
    (found : slots.find? origin = some ⟨w, ref⟩) : slots.origin ref = origin := by
  induction slots generalizing w with
  | nil => cases ref
  | cons current rest ih =>
    by_cases same : origin = current
    · simp only [Slots.find?, same, beq_self_eq_true, ite_true, Option.some.injEq] at found
      cases found
      exact same.symm
    · simp [Slots.find?, same, Option.map_eq_some_iff] at found
      obtain ⟨⟨_, prior⟩, resolved, sameRef⟩ := found
      obtain ⟨rfl, located⟩ := sameRef
      cases (eq_of_heq located)
      exact ih resolved

theorem Slots.find?_exists {slots : Slots widths} {origin : Nat} (found : origin ∈ slots.origins) :
    ∃ ref, slots.find? origin = some ref := by
  induction slots with
  | nil => simp [Slots.origins] at found
  | cons current rest ih =>
    by_cases same : origin = current
    · simp [Slots.find?, same]
    · have inRest : origin ∈ rest.origins := by simpa [Slots.origins, same] using found
      obtain ⟨⟨_, ref⟩, located⟩ := ih inRest
      simp [Slots.find?, same, located]

theorem promote_perm (slots : Slots widths) {header : List Nat} {index origin : Nat}
    (atIndex : header[index]? = some origin) :
    ((Slots.cons (w := w) origin slots).origins ++ header.eraseIdx index).Perm (slots.origins ++ header) := by
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp atIndex
  have chosen : (origin :: header.eraseIdx index).Perm header :=
    eq ▸ List.getElem_cons_eraseIdx_perm bound
  exact List.perm_middle.symm.trans (chosen.append_left _)

theorem origins_agree (values : Env widths) (latch : BitVec carried.val) (input : Env Input) :
    CapturesAgree (origins (carried := carried) widths) ((values.append (.cons latch .nil)).append input)
      (values.append input) := by
  induction values with
  | nil =>
    intro _ ref capture found
    cases ref with
    | here => cases found
    | there ref => cases found; rfl
  | cons value values ih =>
    intro _ ref capture found
    cases ref with
    | here => cases found; rfl
    | there ref =>
      cases h : origins _ ref with
      | inr _ => simp [origins, h, Sum.map] at found
      | inl prior =>
        have translated : Var.there prior = capture := by
          simpa [origins, h, Sum.map] using found
        subst capture
        exact ih ref prior h

theorem immutableOrigins_agree (values : Env widths) (input : Env Input) :
    CapturesAgree (immutableOrigins widths) (values.append input) input := by
  induction values with
  | nil =>
    intro _ ref captured found
    cases found
    rfl
  | cons value values ih =>
    intro _ ref captured found
    cases ref with
    | here => cases found
    | there ref => exact ih ref captured found

theorem immutableOrigins_cut (ref : Var (widths ++ Input) w) {captured : Var Input w}
    (found : immutableOrigins widths ref = .inl captured) : definitionCut widths ref = 0 := by
  induction widths with
  | nil => exact Nat.zero_sub _
  | cons width widths ih =>
    cases ref with
    | here => cases found
    | there ref =>
      change (widths.length + 1) - (ref.index + 1) = 0
      rw [Nat.succ_sub_succ_eq_sub]
      exact ih ref found

theorem prefixRef_get (ref : Var widths w) (values : Env widths) (suffix : Env Input) :
    (values.append suffix).get (prefixRef Input ref) = values.get ref := by
  induction ref with
  | here => cases values; rfl
  | there ref ih => cases values; exact ih _

theorem origins_prefixRef (ref : Var widths w) :
    origins (carried := carried) widths (prefixRef Input (prefixRef [carried] ref)) =
      .inl (prefixRef Input ref) := by
  induction ref with
  | here => rfl
  | there ref ih =>
    change (origins _ (prefixRef Input (prefixRef [carried] ref))).map Var.there id =
      .inl (.there (prefixRef Input ref))
    rw [ih]
    rfl

private theorem prepend_carry (values : Env (extra ++ [saved])) (value : BitVec w.val)
    (frame : Frame (SourceLabel carried result)) :
    prependFrame value (carryFrameWith values frame) = carryFrameWith (extra := w :: extra) (.cons value values) frame := by
  rcases frame with ⟨label, args⟩
  cases label <;> rfl

private theorem prepend_transfer (values : Env (extra ++ [saved])) (value : BitVec w.val)
    (out : Frame (SourceLabel carried result) ⊕ Env [result]) :
    (out.map (carryFrameWith values) id).map (prependFrame value) id =
      out.map (carryFrameWith (extra := w :: extra) (.cons value values)) id := by
  cases out with
  | inl frame => exact congrArg Sum.inl (prepend_carry values value frame)
  | inr returned => rfl

theorem extend_routes
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {source : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {target : Cfg TargetOp (Label saved carried result (w :: extra)) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])} {value : BitVec w.val}
    (prior : RoutesWith base source input values) (step : StepRoutes source target input values value) :
    RoutesWith base target input (extra := w :: extra) (.cons value values) := by
  constructor
  · rw [step.entry, prior.entry, prepend_transfer]
  · intro frame
    have routed := step.block frame
    dsimp only at routed
    rw [prior.block frame, prepend_transfer, prepend_carry] at routed
    exact routed

theorem extend_run_eq
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {source : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {target : Cfg TargetOp (Label saved carried result (w :: extra)) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])} {value : BitVec w.val}
    (prior : RoutesWith base source input values) (step : StepRoutes source target input values value)
    (fuel : Nat) : target.run evalOp fuel input = source.run evalOp fuel input :=
  (routesWith_run_eq (extend_routes prior step) fuel).trans (routesWith_run_eq prior fuel).symm

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Saved
