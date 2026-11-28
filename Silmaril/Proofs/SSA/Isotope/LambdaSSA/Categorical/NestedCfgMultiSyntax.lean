module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.MultiNested.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmissionSyntax
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Thms

/-! # Selected rows and typed transfers in an accepted table -/

public section

universe v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiSyntax

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.MultiNested
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite (branchesTo)

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

private theorem row_checked {form : Option CaseTag} {A : Ty Empty} {out : RouteLayout Empty}
    {r : Region Φ} {p : RowPlan Φ} {mask : Option InnerMask}
    (ok : checkRow? form A out r mask = some p) : p.Valid A out r form := by
  cases form with
  | none =>
      obtain ⟨common, route, rfl⟩ := Option.map_eq_some_iff.mp ok
      exact .ordinary route
  | some tag =>
      simp only [checkRow?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ok
      obtain ⟨selected, choice, plan, typed, rfl⟩ := ok
      exact .nested (NestedCfgAdmissionSyntax.selected_tag choice) (NestedCfgFiniteSyntax.inner_checked typed)

theorem checked {m n : Nat} {keep : Fin m ↪ Fin n} {P : Fin m → Ty Empty} {forms : Fin m → Bool}
    {r : Region Φ} {L : LCtx (Ty Empty)} {p : Plan Φ m n}
    {masks : Fin m → Option InnerMask} {tags : Fin m → CaseTag}
    (ok : check? keep P forms r L masks tags = some p) : p.Valid keep P forms r L tags := by
  simp only [check?, Option.bind_eq_some_iff] at ok
  obtain ⟨outer, ho, ok⟩ := ok
  split at ok <;> try contradiction
  rename_i written
  simp only [Option.bind_eq_some_iff] at ok
  obtain ⟨entry, he, rows, hr, ok⟩ := ok
  split at ok <;> try contradiction
  rename_i all
  cases Option.some.inj ok
  exact ⟨CfgRestriction.check?_sound ho, written, he, fun i => row_checked (Region.checkFamily_some hr i),
    fun i => by simpa using List.all_eq_true.mp all i (List.mem_finRange _)⟩

@[expose] def Fits (A : Ty Empty) (choice : Option CaseTag) (T : Ty Empty) : Prop :=
  match choice with
  | none => T = A
  | some tag => ∃ D, T = tag.sumType A D

theorem target {m : Nat} {P S : Fin m → Ty Empty} {forms : Fin m → Bool} {L : LCtx (Ty Empty)}
    {tags : Fin m → CaseTag} (locals : RouteLayout Empty) {Γ : VCtx (Ty Empty)} {r common : Region Φ}
    (route : r.checkRoutes? (locals ++ layout P forms L tags) Γ = some common)
    (typed : r.HasType Γ (locals.map Prod.fst ++ (List.ofFn S ++ L))) (i : Fin m)
    (edge : branchesTo (locals.length + i.val) common = true) : Fits (P i) (selection forms tags i) (S i) := by
  have hit : (locals ++ layout P forms L tags)[locals.length + i.val]? = some (P i, selection forms tags i) := by
    simp [layout, List.getElem?_append_right, List.getElem?_append_left, i.isLt]
  have actual : (locals.map Prod.fst ++ (List.ofFn S ++ L))[locals.length + i.val]? = some (S i) := by
    simp [List.getElem?_append_right, List.getElem?_append_left, i.isLt]
  have determined := NestedCfgFiniteSyntax.route_target true route edge hit typed
  cases h : selection forms tags i with
  | none =>
      rw [h] at determined
      exact Option.some.inj (actual.symm.trans determined)
  | some tag =>
      rw [h] at determined
      obtain ⟨D, atType⟩ := determined
      exact ⟨D, Option.some.inj (actual.symm.trans atType)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMultiSyntax
