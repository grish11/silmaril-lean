module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Packed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.Syntax
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.Normalization
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.Reflection

/-! # Structural normalization and native reflection for recursive block-free sources -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (inputSlots Difference)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback (Live)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

theorem Code.term_typed {n m : Nat} (c : Code 1 n) (ρ : Fin n → Fin m) :
    Tm.HasType (Live m) (c.term ρ) Bit :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.term_typed c ρ

theorem Code.region_typed {k n m : Nat} (c : Code k n) (ρ : Fin n → Fin m) :
    ValueBranches (Live m) (c.region ρ) (Live k) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.region_typed c ρ

/-- The literal region normalizes at the same interface, with no bound on
let and case depth and with the actual returned slots substituted. -/
theorem Code.normalize_eqv {k n m : Nat} (c : Code k n) (ρ : Fin n → Fin m) :
    Eqv false (Live m) (c.region ρ) (c.normalize ρ).region (Live k) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.replay c ρ

theorem ofStaged_packed (p : BitFragment.Program) : (ofStaged p).packed = p.packed := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff (Step false) (ofStaged p).typed.packExits p.typed.packExits).2
  rw [ofStaged_written]
  exact Paper.Extension.Eqv.refl p.typed.packExits.hasType

theorem Program.packed_replay (p : Program) :
    p.packed = Paper.Extension.Singleton.ofRegion (Step false) (p.tree.written_typed inputSlots).packExits :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.replay_packed p

theorem Program.observations_eq (p : Program) (g : Bool) :
    p.observations g = p.tree.outcomes (fun _ => g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.observations_eq p g

theorem Program.packed_eq_iff_key (p q : Program) : p.packed = q.packed ↔ p.tree.key = q.tree.key :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.packed_eq_iff_key p q

/-- Compare the original packed arrows with native LetCase equality of
the actual acyclic compiler outputs for this recursive grammar. -/
theorem Program.packed_eq_iff_compiled (p q : Program) : p.packed = q.packed ↔ p.CompiledEq q :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.packed_eq_iff_compiled p q

theorem Program.separate_some (p q : Program) {w : Difference} (h : p.tree.separate? q.tree = some w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.separate_some p q h

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive
