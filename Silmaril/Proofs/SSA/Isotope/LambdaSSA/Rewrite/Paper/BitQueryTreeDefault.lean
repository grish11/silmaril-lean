module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Default.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Reflection.Thms

/-! # Native replay and executable comparison in default Paper -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeDefault

open Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.RequestTree
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

theorem default_packed_replay (t : Tree 1) : t.defaultPacked = t.key.defaultPacked :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (.cfgEta (.native (native_packed_replay t)))

theorem default_eq_iff_key (t u : Tree 1) : t.defaultPacked = u.defaultPacked ↔ t.key = u.key := by
  constructor
  · intro eq
    have projected : t.packed = u.packed := congrArg ((Paper.Extension.Singleton.projection Seed).map) eq
    exact (packed_eq_iff_key t u).mp projected
  · intro eq
    exact (default_packed_replay t).trans ((congrArg Tree.defaultPacked eq).trans (default_packed_replay u).symm)

theorem native_packed_eq_iff_key (t u : Tree 1) :
    SubstitutionEquiv [Bit] t.guarded.packExits u.guarded.packExits [packedExitType Exits] ↔
      t.key = u.key := by
  constructor
  · intro eq
    exact (default_eq_iff_key t u).mp ((Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (.cfgEta (.native eq)))
  · intro eq
    exact (native_packed_replay t).trans (eq ▸ (native_packed_replay u).symm)

theorem default_eq_iff_observations (t u : Tree 1) :
    t.defaultPacked = u.defaultPacked ↔ ∀ guard, t.observations guard = u.observations guard :=
  (default_eq_iff_key t u).trans ((packed_eq_iff_key t u).symm.trans (packed_eq_iff_observations t u))

theorem separate_none_iff_default (t u : Tree 1) : t.separate? u = none ↔ t.defaultPacked = u.defaultPacked :=
  (separate_none_iff_packed t u).trans ((packed_eq_iff_key t u).trans (default_eq_iff_key t u).symm)

theorem separate_of_default_ne (t u : Tree 1) (different : t.defaultPacked ≠ u.defaultPacked) :
    ∃ w, t.separate? u = some w ∧
      w.history.observation ∈ (w.source t u).observations w.guard ∧
      w.history.observation ∉ (w.target t u).observations w.guard :=
  separate_of_key_ne t u (fun eq => different ((default_eq_iff_key t u).mpr eq))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeDefault
