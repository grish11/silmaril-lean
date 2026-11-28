module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Default.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Reflection.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeDefault

/-! # Default native equality for the selected Bit request trees -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- The original packed tree and its key are equal in default Paper. -/
theorem default_packed_replay (t : Tree 1) : t.defaultPacked = t.key.defaultPacked :=
  BitQueryTreeDefault.default_packed_replay t

/-- Native substitution equivalence already characterizes the selected packed keys. -/
theorem native_packed_eq_iff_key (t u : Tree 1) :
    SubstitutionEquiv [Bit] t.guarded.packExits u.guarded.packExits [packedExitType Exits] ↔
      t.key = u.key :=
  BitQueryTreeDefault.native_packed_eq_iff_key t u

/-- The forward direction uses the quotient projection. Native replay
supplies the reverse direction at these original packed representatives. -/
theorem default_eq_iff_key (t u : Tree 1) : t.defaultPacked = u.defaultPacked ↔ t.key = u.key :=
  BitQueryTreeDefault.default_eq_iff_key t u

theorem default_eq_iff_observations (t u : Tree 1) :
    t.defaultPacked = u.defaultPacked ↔ ∀ guard, t.observations guard = u.observations guard :=
  BitQueryTreeDefault.default_eq_iff_observations t u

/-- The existing executable search decides equality of the original default arrows. -/
theorem separate_none_iff_default (t u : Tree 1) : t.separate? u = none ↔ t.defaultPacked = u.defaultPacked :=
  BitQueryTreeDefault.separate_none_iff_default t u

theorem separate_of_default_ne (t u : Tree 1) (different : t.defaultPacked ≠ u.defaultPacked) :
    ∃ w, t.separate? u = some w ∧
      w.history.observation ∈ (w.source t u).observations w.guard ∧
      w.history.observation ∉ (w.target t u).observations w.guard :=
  BitQueryTreeDefault.separate_of_default_ne t u different

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree
