module

public import Silmaril.Languages.Python.Core.Locals.Defs
public import Silmaril.Languages.Python.Core.Context.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Locals

open Silmaril.Languages.Python.Core.Locals Silmaril.Semantics.Operational
open Silmaril.Languages.Python.Core (Expr)

variable {slots : Nat} {store : Store slots} {rhs : Rhs slots} {cont : Continuation slots}
  {source target : State slots} {label : Option (Event slots)}

private theorem literal_iff {value : Int} :
    rhs.literal? = some value ↔ rhs = .arithmetic (.int value) := by
  cases rhs with
  | arithmetic expr => cases expr <;> simp [Rhs.literal?]
  | read | binary | logical => simp [Rhs.literal?]

private theorem step_not_literal {next : Except (Error slots) (Rhs slots)}
    (step : rhs.Step store next) : rhs.literal? = none := by
  cases test : rhs.literal? with
  | none => rfl
  | some value =>
    obtain rfl := literal_iff.mp test
    cases step with
    | arithmetic core => cases core

private theorem reduce_sound {next : Except (Error slots) (Rhs slots)}
    (reduced : rhs.reduce store = some next) : rhs.Step store next := by
  induction rhs generalizing next with
  | arithmetic expr =>
    obtain ⟨inner, calculation, rfl⟩ := Option.map_eq_some_iff.mp reduced
    exact .arithmetic (Silmaril.Languages.Python.Core.Context.reduce_iff.mp calculation)
  | read slot =>
    cases loaded : store slot with
    | none =>
      simp [Rhs.reduce, Rhs.load, loaded, Except.map] at reduced
      subst next
      exact .unbound slot loaded
    | some value =>
      simp [Rhs.reduce, Rhs.load, loaded, Except.map] at reduced
      subst next
      exact .load slot value loaded
  | binary op left right leftIH rightIH =>
    rw [Rhs.reduce] at reduced
    cases lhs : left.literal? with
    | none =>
      rw [lhs] at reduced
      obtain ⟨inner, calculation, rfl⟩ := Option.map_eq_some_iff.mp reduced
      exact .left (leftIH calculation)
    | some a =>
      cases rhs : right.literal? with
      | none =>
        rw [lhs, rhs] at reduced
        obtain ⟨inner, calculation, rfl⟩ := Option.map_eq_some_iff.mp reduced
        obtain rfl := literal_iff.mp lhs
        exact .right (rightIH calculation)
      | some b =>
        rw [lhs, rhs] at reduced
        have eq := Option.some.inj reduced
        rw [← eq]
        obtain rfl := literal_iff.mp lhs
        obtain rfl := literal_iff.mp rhs
        exact .compute (Silmaril.Languages.Python.Core.BinOp.eval_iff.mp rfl)
  | logical op left right leftIH rightIH =>
    rw [Rhs.reduce] at reduced
    cases lhs : left.literal? with
    | none =>
      rw [lhs] at reduced
      obtain ⟨inner, calculation, rfl⟩ := Option.map_eq_some_iff.mp reduced
      exact .logicalTest (leftIH calculation)
    | some value =>
      rw [lhs] at reduced
      obtain rfl := literal_iff.mp lhs
      cases chosen : op.runsRight value with
      | false =>
        simp [chosen] at reduced
        subst next
        exact .logicalShort chosen
      | true =>
        simp [chosen] at reduced
        subst next
        exact .logicalRight chosen

private theorem reduce_complete {next : Except (Error slots) (Rhs slots)}
    (step : rhs.Step store next) : rhs.reduce store = some next := by
  induction step with
  | arithmetic step =>
    simp [Rhs.reduce, Silmaril.Languages.Python.Core.Context.reduce_iff.mpr step]
  | load slot value loaded => simp [Rhs.reduce, Rhs.load, loaded, Except.map]
  | unbound slot loaded => simp [Rhs.reduce, Rhs.load, loaded, Except.map]
  | left step ih => rw [Rhs.reduce, step_not_literal step, ih]; rfl
  | @right op left right next step ih =>
    have literal : (Rhs.arithmetic (.int left) : Rhs slots).literal? = some left := rfl
    rw [Rhs.reduce, literal, step_not_literal step, ih]
    rfl
  | compute step =>
    simp [Rhs.reduce, Rhs.literal?, Silmaril.Languages.Python.Core.BinOp.eval_iff.mpr step]
  | logicalTest step ih => rw [Rhs.reduce, step_not_literal step, ih]; rfl
  | logicalShort chosen => simp [Rhs.reduce, Rhs.literal?, chosen]
  | logicalRight chosen => simp [Rhs.reduce, Rhs.literal?, chosen]

theorem reduce_iff {next : Except (Error slots) (Rhs slots)} :
    rhs.reduce store = some next ↔ rhs.Step store next :=
  ⟨reduce_sound, reduce_complete⟩

private theorem advance_reduction
    (selected : (rhs.reduce store).map (fun next => (none, State.resume store cont next)) =
      some (label, target)) :
    Step (.evaluating store rhs cont) label target := by
  obtain ⟨next, reduced, eq⟩ := Option.map_eq_some_iff.mp selected
  cases eq
  exact .expression (reduce_iff.mp reduced)

theorem advance_iff : source.advance = some (label, target) ↔ Step source label target := by
  constructor
  · intro selected
    cases source with
    | evaluating store rhs cont =>
      cases rhs with
      | read slot => exact advance_reduction (rhs := .read slot) selected
      | binary op left right => exact advance_reduction (rhs := .binary op left right) selected
      | logical op left right => exact advance_reduction (rhs := .logical op left right) selected
      | arithmetic expr =>
        cases expr with
        | binary op left right =>
          exact advance_reduction (rhs := .arithmetic (.binary op left right)) selected
        | int value =>
          cases cont with
          | ret =>
            cases selected
            exact .ret store value
          | assign slot rest =>
            cases selected
            exact .assign store slot value rest
          | branch yes no =>
            change some (none, State.enter store (if value = 0 then no else yes)) =
              some (label, target) at selected
            by_cases zero : value = 0
            · subst value
              cases selected
              exact .takeNo store yes no
            · simp only [zero, ite_false] at selected
              cases selected
              exact .takeYes store value yes no zero
    | raising store error =>
      cases selected
      exact .raise store error
    | finished => simp [State.advance] at selected
  · intro step
    cases step with
    | @expression store rhs cont next reduced =>
      cases rhs with
      | read | binary | logical => simp [State.advance, reduce_iff.mpr reduced]
      | arithmetic expr =>
        cases expr with
        | binary => simp [State.advance, reduce_iff.mpr reduced]
        | int =>
          cases reduced with
          | arithmetic core => cases core
    | takeYes store value yes no nonzero => simp [State.advance, nonzero]
    | takeNo | assign | ret | raise => rfl

theorem deterministic {other : State slots} {otherLabel : Option (Event slots)}
    (left : Step source label target) (right : Step source otherLabel other) :
    label = otherLabel ∧ target = other :=
  Prod.mk.inj (Option.some.inj ((advance_iff.mpr left).symm.trans (advance_iff.mpr right)))

theorem detFrom (start : State slots) : (ordinary slots).DetFrom start := by
  intro source _
  constructor
  · rintro left right ⟨_, l⟩ ⟨_, r⟩
    exact (deterministic l r).2
  · intro left right l r
    cases l
    cases r
    rfl

theorem terminal (slots : Nat) : (ordinary slots).TerminalDiscipline := by
  intro source outcome observed target edge
  obtain ⟨_, step⟩ := edge
  cases observed
  cases step

private theorem rhs_progress (store : Store slots) (rhs : Rhs slots) :
    (∃ value, rhs = .arithmetic (.int value)) ∨ ∃ next, rhs.Step store next := by
  induction rhs with
  | read slot =>
    apply Or.inr
    cases loaded : store slot with
    | none => exact ⟨_, .unbound slot loaded⟩
    | some value => exact ⟨_, .load slot value loaded⟩
  | arithmetic expr =>
    cases selected : Silmaril.Languages.Python.Core.Context.focus expr with
    | value value =>
      have source := Silmaril.Languages.Python.Core.Context.focus_source expr
      rw [selected] at source
      exact Or.inl ⟨value, congrArg Rhs.arithmetic source.symm⟩
    | redex frames redex =>
      have step : expr.Step (Silmaril.Languages.Python.Core.Context.resume frames redex.contract) :=
        Silmaril.Languages.Python.Core.Context.reduce_iff.mp (by
          simp [Silmaril.Languages.Python.Core.Context.reduce, selected])
      exact Or.inr ⟨_, .arithmetic step⟩
  | binary op left right leftIH rightIH =>
    apply Or.inr
    rcases leftIH with ⟨a, rfl⟩ | ⟨next, step⟩
    · rcases rightIH with ⟨b, rfl⟩ | ⟨next, step⟩
      · exact ⟨_, .compute (Silmaril.Languages.Python.Core.BinOp.eval_iff.mp rfl)⟩
      · exact ⟨_, .right step⟩
    · exact ⟨_, .left step⟩
  | logical op left right leftIH _ =>
    apply Or.inr
    rcases leftIH with ⟨value, rfl⟩ | ⟨next, step⟩
    · cases chosen : op.runsRight value with
      | false => exact ⟨_, .logicalShort chosen⟩
      | true => exact ⟨_, .logicalRight chosen⟩
    · exact ⟨_, .logicalTest step⟩

theorem progress (state : State slots) :
    (∃ label target, Step state label target) ∨ ∃ result, Observes state (.returned result) := by
  cases state with
  | evaluating store rhs cont =>
    apply Or.inl
    rcases rhs_progress store rhs with ⟨value, rfl⟩ | ⟨next, step⟩
    · cases cont with
      | ret => exact ⟨_, _, .ret store value⟩
      | assign slot rest => exact ⟨_, _, .assign store slot value rest⟩
      | branch yes no =>
        by_cases zero : value = 0
        · subst value
          exact ⟨_, _, .takeNo store yes no⟩
        · exact ⟨_, _, .takeYes store value yes no zero⟩
    · exact ⟨_, _, .expression step⟩
  | raising store error => exact Or.inl ⟨_, _, .raise store error⟩
  | finished store result => exact Or.inr ⟨_, .finished store result⟩

private theorem decision_valid {selection : Option (Option (Event slots) × State slots)}
    (calculation : source.advance = selection) :
    (selection.elim (.stop .unknown) fun transition => Decision.move transition.2).Valid
      (model slots).semantics source := by
  cases selection with
  | none => trivial
  | some transition =>
    obtain ⟨label, target⟩ := transition
    exact ⟨label, advance_iff.mp calculation⟩

theorem pick_valid (state : State slots) : state.pick.Valid (model slots).semantics state := by
  cases state with
  | evaluating store rhs cont => exact decision_valid (source := .evaluating store rhs cont) rfl
  | raising store error => exact decision_valid (source := .raising store error) rfl
  | finished store result => exact .finished store result

theorem pick_known (state : State slots) : state.pick ≠ .stop .unknown := by
  cases state with
  | evaluating store rhs cont =>
    rcases progress (.evaluating store rhs cont) with ⟨label, target, edge⟩ | ⟨result, observed⟩
    · simp [State.pick, advance_iff.mpr edge, Option.elim]
    · cases observed
  | raising store error => simp [State.pick, State.advance, Option.elim]
  | finished store result => simp [State.pick]

end Silmaril.Proofs.Languages.Python.Core.Locals
