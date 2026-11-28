module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Nested.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplay

/-! # Stability and typed pullback of a single nested-entry hoist -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NestedReplay

open WithEntryLet (Site)

variable {Φ : Type v}

/-- Substituting the outer captures in each re-entry continuation gives
the re-entry family of the substituted outer rows. Each row retains its
local payload under the lifted substitution. -/
theorem map_cfgEntryContinuations {n : Nat} (outer : Fin n → Region Φ) (θ : Nat → Tm Φ) :
    mapLSubstVars θ (cfgEntryContinuations outer) =
      cfgEntryContinuations (fun j => (outer j).substVars (Tm.liftSubst θ)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplay.map_cfgEntryContinuations outer θ

/-- The same address and hoisted syntax commute with value substitution. -/
theorem hoistAt_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    hoistAt site (r.substVars θ) = (hoistAt site r).map (·.substVars θ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplay.hoistAt_substVars site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Keep the entire inner label prefix. The outer labels disappear from
the exit interface, while the outward exits retain their original types. -/
theorem liftedReentry_hasType {m n : Nat} {outer : Fin n → Region Φ}
    (S : Fin m → τ) (R : Fin n → τ)
    (ho : ∀ j, HasType (R j :: Γ) (outer j) (List.ofFn R ++ L)) :
    LSubst.HasType Γ (List.ofFn S ++ (List.ofFn R ++ L)) (List.ofFn S ++ L)
      (liftLSubstN m (cfgEntryContinuations outer)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplay.liftedReentry_hasType S R ho

/-- The addressed move retains the exact context and exit interface. -/
theorem hoistAt_exact (site : Site) (hr : HasType Γ r L) (hm : hoistAt site r = some s) :
    HasType Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplay.hoistAt_exact site hr hm

/-- Pull back a successful hoist to the same address before substitution. -/
theorem hoistAt_pullback (site : Site) (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (hm : hoistAt site (r.substVars θ) = some s) :
    ∃ q, hoistAt site r = some q ∧ s = q.substVars θ ∧
      HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplay.hoistAt_pullback site hr θ hm

/-- Guarded inputs keep constructor-valued branch arguments through
the same lifted outward continuation substitution. -/
theorem hoistAt_guarded (site : Site) (hr : ValueBranches Γ r L) (hm : hoistAt site r = some s) :
    ValueBranches Γ s L ∧ WithBoundEntryEta.Eqv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.NestedReplay.hoistAt_guarded site hr hm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.NestedReplay
