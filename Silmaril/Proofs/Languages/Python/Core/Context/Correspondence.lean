module

public import Silmaril.Languages.Python.Core.Context.Defs
public import Silmaril.Languages.Python.Core.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Context

open Silmaril.Languages.Python.Core Silmaril.Languages.Python.Core.Context

theorem focus_source (expr : Expr) : (focus expr).expr = expr := by
  induction expr with
  | int value => rfl
  | binary op left right leftIH rightIH =>
    cases lhs : focus left with
    | value a =>
      rw [lhs] at leftIH
      cases rhs : focus right <;> rw [focus, lhs, rhs] <;>
        rw [rhs] at rightIH <;> exact congrArg₂ (Expr.binary op) leftIH rightIH
    | redex frames redex =>
      rw [lhs] at leftIH
      rw [focus, lhs]
      exact congrArg (fun expr => Expr.binary op expr right) leftIH

theorem focus_plug (frames : List Frame) (redex : Redex) :
    focus (plug frames redex.expr) = .redex frames redex := by
  induction frames with
  | nil => cases redex; rfl
  | cons frame rest ih =>
    cases frame <;> simp [plug, Frame.plug, focus, ih]

theorem focus_iff {frames : List Frame} {redex : Redex} {expr : Expr} :
    focus expr = .redex frames redex ↔ plug frames redex.expr = expr := by
  constructor
  · intro eq
    simpa only [eq, View.expr] using focus_source expr
  · rintro rfl
    exact focus_plug frames redex

theorem plug_step (frames : List Frame) {expr : Expr} {next : Except Exception Expr}
    (step : expr.Step next) : (plug frames expr).Step (resume frames next) := by
  induction frames with
  | nil => cases next <;> exact step
  | cons frame rest ih =>
    cases frame with
    | left op right =>
      have lifted := Expr.Step.left (op := op) (right := right) ih
      cases next <;> exact lifted
    | right op left =>
      have lifted := Expr.Step.right (op := op) (left := left) ih
      cases next <;> exact lifted

private theorem decomposes_step {source : Expr} {next : Except Exception Expr} (step : source.Step next) :
    Reduces source next := by
  induction step with
  | @left op left right next _ ih =>
    obtain ⟨frames, redex, result, place, arithmetic, eq⟩ := ih
    refine ⟨.left op right :: frames, redex, result, ?_, arithmetic, ?_⟩
    · exact congrArg (fun expr => Expr.binary op expr right) place
    · rw [eq]
      cases result <;> rfl
  | @right op left right next _ ih =>
    obtain ⟨frames, redex, result, place, arithmetic, eq⟩ := ih
    refine ⟨.right op left :: frames, redex, result, ?_, arithmetic, ?_⟩
    · exact congrArg (Expr.binary op (.int left)) place
    · rw [eq]
      cases result <;> rfl
  | @compute op left right result arithmetic =>
    exact ⟨[], ⟨op, left, right⟩, result, rfl, arithmetic, by cases result <;> rfl⟩

theorem reduces_iff {expr : Expr} {next : Except Exception Expr} : Reduces expr next ↔ expr.Step next :=
  ⟨fun ⟨frames, _, _, place, arithmetic, eq⟩ => place ▸ eq.symm ▸ plug_step frames (.compute arithmetic),
    decomposes_step⟩

private theorem reduce_iff_reduces {expr : Expr} {next : Except Exception Expr} :
    reduce expr = some next ↔ Reduces expr next := by
  constructor
  · intro selected
    cases located : focus expr with
    | value => simp [reduce, located] at selected
    | redex frames redex =>
      have eq := Option.some.inj (show some (resume frames redex.contract) = some next from
        by simpa only [reduce, located] using selected)
      exact ⟨frames, redex, redex.op.eval redex.left redex.right, focus_iff.mp located,
        BinOp.eval_iff.mp rfl, eq.symm⟩
  · rintro ⟨frames, redex, result, rfl, arithmetic, rfl⟩
    simp only [reduce, focus_plug, Redex.contract, BinOp.eval_iff.mpr arithmetic]

theorem reduce_iff {expr : Expr} {next : Except Exception Expr} :
    reduce expr = some next ↔ expr.Step next :=
  reduce_iff_reduces.trans reduces_iff

theorem reduce_eq_core (expr : Expr) : reduce expr = expr.reduce := by
  cases selected : reduce expr with
  | none =>
    cases native : expr.reduce with
    | none => rfl
    | some next =>
      have impossible := reduce_iff.mpr (Expr.reduce_iff.mp native)
      rw [selected] at impossible
      cases impossible
  | some next => exact (Expr.reduce_iff.mpr (reduce_iff.mp selected)).symm

theorem advance_eq_core (state : State) : advance state = state.advance := by
  cases state with
  | returning expr => cases expr <;> simp [advance, State.advance, reduce_eq_core]
  | raising => rfl
  | finished => rfl

end Silmaril.Proofs.Languages.Python.Core.Context
