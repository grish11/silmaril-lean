module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Native.Retained.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs

/-! # A request followed by a nonconstant retained-bit update -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained.Example

open CategoryTheory CategoryTheory.Limits
open EntryLetObstruction (U)
open SequencingObstruction (Instruction)
open Paper.TypeCategory (ofType)

abbrev Bit : Ty Empty := Silmaril.coprod U U
abbrev TaggedBit : Ty Empty := Silmaril.coprod Bit Bit
abbrev Output : Ty Empty := Silmaril.coprod U Bit
abbrev A := ofType (Φ := Instruction) Bit
abbrev B := ofType (Φ := Instruction) U

def rows : Fin 2 → Region Instruction :=
  Fin.cases (.br 2 (.inr .unit)) (fun _ => .br 2 (.inl .unit))

/-- Execute the visible request, inspect the original bit, then flip it. -/
def update : Region Instruction :=
  letCaseTable (.op .tick .unit) (.var 1) (.br 0 (.var 0)) (.br 1 (.var 0)) rows

theorem update_guarded : ValueBranches [Bit] update [Bit] :=
  letCaseTable_guarded (fun _ : Fin 2 => U) (.op .unit) (.var (i := 1) rfl)
    (.br (ℓ := 0) rfl (.var rfl)) (.br (ℓ := 1) rfl (.var rfl))
    (Fin.cases (.br (ℓ := 2) rfl (.inr .unit)) (fun _ => .br (ℓ := 2) rfl (.inl .unit)))

def once : Region Instruction := repeating update (.var 0)
def twice : Region Instruction :=
  repeating (compLSubst (fun _ => update) (fun _ => update) 0) (.var 0)

theorem once_guarded : ValueBranches [Bit] once [Output] :=
  repeating_guarded update_guarded (.var rfl)

theorem twice_guarded : ValueBranches [Bit] twice [Output] :=
  repeating_guarded (CfgEta.TypeCategory.seqValueBranches update_guarded update_guarded) (.var rfl)

noncomputable abbrev g : A ⟶ B ⨿ A := single update_guarded
noncomputable abbrev g₂ : A ⟶ B ⨿ A := g ≫ coprod.desc coprod.inl g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NativeFrame.Retained.Example
