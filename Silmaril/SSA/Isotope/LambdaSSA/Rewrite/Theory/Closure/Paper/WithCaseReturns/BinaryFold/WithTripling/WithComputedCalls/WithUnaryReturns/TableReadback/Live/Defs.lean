module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Assembly.Thms

/-! # The written live two-row table -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live

open Silmaril Silmaril.Isotope.LambdaSSA

abbrev Atom := ULift.{1} Unit
abbrev Payload : Ty Atom := .base ⟨()⟩
abbrev Reply : Ty Atom := coprod Silmaril.unit Payload
abbrev Result : Ty Atom := coprod Payload (product Payload Payload)

inductive Op where
  | enter
  | poll

instance : HasTy Op (Ty Atom) where
  src _ := Payload
  trg
    | .enter => Payload
    | .poll => Reply

instance : HasEff Op Bool where
  eff _ := true

def labels : Fin 2 → Ty Atom := fun i => if i.val = 0 then Payload else Silmaril.unit

def entry : Region Op := .let₁ (.op .enter (.var 0)) (.br 0 (.var 0))

def pollRow : Region Op :=
  .let₁ (.op .poll (.var 0))
    (.case (.var 0) (.br 1 (.var 0)) (.br 2 (.inr (.pair (.var 3) (.var 0)))))

/-- The second row resets the next request argument to the retained input. -/
def rows : Fin 2 → Region Op := fun i => if i.val = 0 then pollRow else .br 0 (.var 1)

def written : Region Op := .cfg entry 2 rows

theorem entry_typed : ValueBranches [Payload] entry (List.ofFn labels ++ [Result]) :=
  .let₁ (.op (.var (i := 0) rfl)) (.br (ℓ := 0) rfl (.var (i := 0) rfl))

theorem rows_typed (i : Fin 2) : ValueBranches [labels i, Payload] (rows i) (List.ofFn labels ++ [Result]) := by
  have row0 : ValueBranches [labels 0, Payload] (rows 0) (List.ofFn labels ++ [Result]) :=
    .let₁ (.op (.var (i := 0) rfl)) (.case (.var (i := 0) rfl)
      (.br (ℓ := 1) rfl (.var (i := 0) rfl))
      (.br (ℓ := 2) rfl (.inr (.pair (.var (i := 3) rfl) (.var (i := 0) rfl)))))
  have row1 : ValueBranches [labels 1, Payload] (rows 1) (List.ofFn labels ++ [Result]) :=
    .br (ℓ := 0) rfl (.var (i := 1) rfl)
  refine Fin.cases row0 (fun j => ?_) i
  have eq : j = 0 := Subsingleton.elim _ _
  exact eq.symm ▸ row1

theorem written_typed : ValueBranches [Payload] written [Result] :=
  .cfg labels entry_typed rows_typed

open Silmaril.Isotope (Value)

/-- The first poll takes the backedge. The second poll receives the original
capture as its operand and returns the outward value. The state records the
requests already performed, in order. -/
inductive Replies : Op → Value Nat → List Op → Value Nat → List Op → Prop
  | entry (x y : Nat) : Replies .enter (.atom x) [] (.atom y) [.enter]
  | repeat (y : Nat) : Replies .poll (.atom y) [.enter] (.inl .unit) [.enter, .poll]
  | exit (x z : Nat) : Replies .poll (.atom x) [.enter, .poll] (.inr (.atom z)) [.enter, .poll, .poll]

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live
