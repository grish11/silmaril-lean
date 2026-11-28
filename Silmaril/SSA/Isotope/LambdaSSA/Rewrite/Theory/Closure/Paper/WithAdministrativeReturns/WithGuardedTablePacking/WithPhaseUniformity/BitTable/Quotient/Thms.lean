module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Quotient.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Mixed.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Composite.Completion.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.ClassSeparation

/-! # Replay along any surjective class map between request tables

## Proved

* `Table.class_square`: a map of states `cls` that preserves the row
  programs and commutes with the successors is a simulation, as one
  equation of default Paper. Its state map is `classFold State cls`,
  which sends state `i` to state `cls i` (`Table.entry_classFold`).
* `Table.quotient_eqv`: if `cls` is also surjective, the table entered at
  state `i` equals the target table entered at `cls i` in
  `WithPhaseUniformity`. The classes may have any sizes and the source
  states may be written in any order. Onto one state this is
  `Table.single_eqv`; onto more it is `class_fold_uniform`.
* `Table.quotient_replay`: two tables over the same target are equal at
  entries of the same class.
* `uneven_eqv`: the regression. Six states `c a c b c b`, with one, two
  and three duplicates, equal the three-state cycle.
* `uneven_ne`: with another label at the `c` duplicate reached after one
  backedge the tables differ. The separating run has two requests
  (`uneven_witness`).

## Not proved

* A class map that is not surjective is not handled here. It is
  `Table.morphism_eqv` in `BitTable/Bisimulation/Thms.lean`.
* Rows other than a program step followed by the routing case, and
  tables of a different shape such as the relay rows.
* The separation is computed in the four-reply interpreter. It only
  refutes an equation. Nothing is claimed about packed dispatchers in
  general, and no completeness is claimed.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion sumIso classFold)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (event)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity

variable {K K' : Nat}

/-! ## Any surjective class map -/

/-- The class map sends the entry at state `i` to the entry at `cls i`. -/
theorem Table.entry_classFold (cls : Fin (K + 1) → Fin (K' + 1)) (i : Fin (K + 1)) :
    ofRegion (entry_typed K i) ≫ classFold (Φ := signature.Instr) State cls = ofRegion (entry_typed K' (cls i)) :=
  Tables.class_inj cls i

/-- The one overall square, an equation of default Paper. -/
theorem Table.class_square (t : Table K) (t' : Table K') (cls : Fin (K + 1) → Fin (K' + 1))
    (hprog : ∀ i, t.prog i = t'.prog (cls i)) (hnext : ∀ i, cls (t.next i) = t'.next (cls i)) :
    (ofRegion t.step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) (classFold State cls) =
      classFold State cls ≫ (ofRegion t'.step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) :=
  Tables.class_square t t' cls hprog hnext

/-- A table entered at any state equals its quotient by a surjective class
map, entered at the state's class. -/
theorem Table.quotient_eqv (t : Table K) (t' : Table K') (cls : Fin (K + 1) → Fin (K' + 1))
    (surj : Function.Surjective cls) (hprog : ∀ i, t.prog i = t'.prog (cls i))
    (hnext : ∀ i, cls (t.next i) = t'.next (cls i)) (i : Fin (K + 1)) :
    Eqv false [State] (t.entered i) (t'.entered (cls i)) [Bit] :=
  Tables.quotient_eqv t t' cls surj hprog hnext i

/-- Replay: two tables with the same quotient are equal at entries of the
same class. Their sizes, layouts and wirings may differ. -/
theorem Table.quotient_replay {K₁ K₂ : Nat} (t₁ : Table K₁) (t₂ : Table K₂) (t' : Table K')
    (c₁ : Fin (K₁ + 1) → Fin (K' + 1)) (c₂ : Fin (K₂ + 1) → Fin (K' + 1))
    (s₁ : Function.Surjective c₁) (s₂ : Function.Surjective c₂)
    (p₁ : ∀ i, t₁.prog i = t'.prog (c₁ i)) (p₂ : ∀ i, t₂.prog i = t'.prog (c₂ i))
    (n₁ : ∀ i, c₁ (t₁.next i) = t'.next (c₁ i)) (n₂ : ∀ i, c₂ (t₂.next i) = t'.next (c₂ i))
    (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1)) (same : c₁ i₁ = c₂ i₂) :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  (t₁.quotient_eqv t' c₁ s₁ p₁ n₁ i₁).trans (same ▸ (t₂.quotient_eqv t' c₂ s₂ p₂ n₂ i₂).symm)

/-- Validity in every supported model, as a consequence of the equation. -/
theorem Table.quotient_valid (t : Table K) (t' : Table K') (cls : Fin (K + 1) → Fin (K' + 1))
    (surj : Function.Surjective cls) (hprog : ∀ i, t.prog i = t'.prog (cls i))
    (hnext : ∀ i, cls (t.next i) = t'.next (cls i)) (i : Fin (K + 1)) :
    Valid (t.entered_typed i).hasType (t'.entered_typed (cls i)).hasType :=
  valid_of_eqv false (t.quotient_eqv t' cls surj hprog hnext i) _ _

/-! ## One, two and three duplicates -/

theorem unevenClass_surjective : Function.Surjective unevenClass :=
  Tables.unevenClass_surjective

/-- The six-state table entered at any state equals the three-state cycle
entered at the state's class. The programs are arbitrary. -/
theorem uneven_eqv (qa qb qc : Program) (i : Fin 6) :
    Eqv false [State] ((Table.uneven qa qb qc).entered i)
      ((Table.cycle3 qa qb qc).entered (unevenClass i)) [Bit] :=
  Tables.uneven_eqv qa qb qc i

/-- Entries of one class are equal: the transient `b₅ → c₂` against the
states on the cycle. -/
theorem uneven_replay (qa qb qc : Program) (i i' : Fin 6) (same : unevenClass i = unevenClass i') :
    Eqv false [State] ((Table.uneven qa qb qc).entered i) ((Table.uneven qa qb qc).entered i') [Bit] :=
  (uneven_eqv qa qb qc i).trans (same ▸ (uneven_eqv qa qb qc i').symm)

/-- A run of the variant entered at state five: the `b` poll repeats and
the poll at state two returns. -/
theorem uneven_witness (a b c d : Poll) (g s r : Bool) :
    (Except.ok (bit r), FreeMonoid.of (event b.label g (!b.returnRight, s)) *
      FreeMonoid.of (event d.label s (d.returnRight, r))) ∈
      (Table.unevenWith a.program b.program c.program d.program).observations 5 g :=
  TableModel.repeat_return _ 5 b d rfl rfl g s r

/-- With another label at the `c` duplicate reached after one backedge,
the six-state table is not equal to the cycle. -/
theorem uneven_ne {a b c d : Poll} (ha : a.label = b.label) (hc : c.label = b.label)
    (other : d.label ≠ b.label) :
    ¬ Eqv false [State] ((Table.unevenWith a.program b.program c.program d.program).entered 5)
      ((Table.cycle3 a.program b.program c.program).entered 1) [Bit] :=
  TableModel.uneven_ne ha hc other

/-- Nor to the six-state table of the three classes. -/
theorem uneven_ne_uneven {a b c d : Poll} (ha : a.label = b.label) (hc : c.label = b.label)
    (other : d.label ≠ b.label) :
    ¬ Eqv false [State] ((Table.unevenWith a.program b.program c.program d.program).entered 5)
      ((Table.uneven a.program b.program c.program).entered 5) [Bit] :=
  fun e => uneven_ne ha hc other (e.trans (uneven_eqv a.program b.program c.program 5))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
