module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmissionSyntax
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Thms

/-! # Finite traversal and exact input-type readback -/

public section

universe v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

theorem inner_checked {k n : Nat} {keep : Fin (k + 1) ↪ Fin (n + 1)} {P : Fin (k + 1) → Ty Empty}
    {body : Region Φ} {p : InnerPlan Φ (k + 1) (n + 1)} {A : Ty Empty} {out : RouteLayout Empty}
    (ok : checkInner? keep P A out body = some p) : p.Valid keep P A out body := by
  simp only [checkInner?, Option.bind_eq_some_iff] at ok
  obtain ⟨table, ht, entry, he, rows, hr, ok⟩ := ok
  split at ok <;> try contradiction
  rename_i all
  cases Option.some.inj ok
  exact ⟨CfgRestriction.check?_sound ht, he, Region.checkFamily_some hr,
    fun i => by simpa using List.all_eq_true.mp all i (List.mem_finRange _)⟩

theorem valid {k n : Nat} {keep : Fin (k + 1) ↪ Fin (n + 1)} {P : Fin (k + 1) → Ty Empty}
    {r : Region Φ} {p : Plan Φ (k + 1) (n + 1)} {L : LCtx (Ty Empty)}
    (ok : check? keep P r L = some p) : p.Valid keep P r L := by
  simp only [check?] at ok
  split at ok <;> try contradiction
  rename_i blocks
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at ok
  obtain ⟨payload, init, body, chosen, p, h, rfl⟩ := ok
  have i := inner_checked h
  have sc : ∀ j, (p.table.rows j).LabelsBound (k + 1 + (L.length + 1)) := by
    simpa only [enclosingLayout, List.length_cons, List.length_map] using i.table.rowScope
  refine ⟨?_, init, ?_, ?_, sc, i.entryRoute, i.rowRoutes, i.paths⟩
  · congr 1
    funext j
    cases Subsingleton.elim j (0 : Fin 1)
    rfl
  · have prune := NestedCfgAdmissionSyntax.selected chosen
    rw [← i.table.source] at prune
    exact prune
  · simpa only [enclosingLayout, List.length_cons, List.length_map] using i.table.entryScope

private theorem branch_type {Γ K : List (Ty Empty)} {i : Nat} {a : Tm Φ} {A : Ty Empty}
    (unique : TypeDetermined Γ a A) (typed : (Region.br i a).HasType Γ K) : At K i A := by
  cases typed with
  | br hit arg => simpa only [unique _ arg] using hit

private theorem case_types {Γ K : List (Ty Empty)} {a : Tm Φ} {l r : Region Φ} {A B : Ty Empty}
    (unique : TypeDetermined Γ a (.coprod A B)) (typed : (Region.case a l r).HasType Γ K) :
    l.HasType (A :: Γ) K ∧ r.HasType (B :: Γ) K := by
  cases typed with
  | case test yes no =>
      obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (unique _ test)
      exact ⟨yes, no⟩

/-- Recover the payload type and tag at a checked transfer in an exact witness. -/
theorem route_target {layout : RouteLayout Empty} {Γ K : List (Ty Empty)} {r s : Region Φ}
    {i : Nat} {A : Ty Empty} (wide : Bool) {tag : Option CaseTag} (ok : r.checkRoutes? layout Γ = some s)
    (target : branchesTo i s = true) (localType : layout[i]? = some (A, tag))
    (typed : (if wide then r else s).HasType Γ K) :
    match if wide then tag else none with | none => At K i A | some t => ∃ D, At K i (t.sumType A D) := by
  induction r generalizing Γ s with
  | br j a =>
      cases hit : layout[j]? with
      | none => simp [Region.checkRoutes?, hit] at ok
      | some route =>
          obtain ⟨B, tag⟩ := route
          simp only [Region.checkRoutes?, hit, Option.bind_eq_some_iff] at ok
          obtain ⟨b, payload, rest⟩ := ok
          cases found : b.synthRouteType? Γ with
          | none => simp [found] at rest
          | some T =>
              simp only [found] at rest
              split at rest <;> try contradiction
              rename_i eq
              subst T
              cases Option.some.inj rest
              have ji : j = i := beq_iff_eq.mp target
              subst j
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hit.symm.trans localType))
              have unique := (Tm.synthRouteType?_sound found).2.1
              cases tag with
              | none =>
                  cases Option.some.inj payload
                  cases wide <;> exact branch_type unique typed
              | some tag =>
                  cases wide
                  · exact branch_type unique typed
                  · have eq : a = tag.inject b := by
                      cases tag <;> cases a <;> first | contradiction | cases Option.some.inj payload; rfl
                    subst a
                    cases tag <;> cases typed with
                    | br lookup ht =>
                        cases ht
                        rename_i h
                        exact ⟨_, (unique _ h) ▸ lookup⟩
  | case a l r il ir =>
      cases found : a.synthRouteType? Γ with
      | none => simp [Region.checkRoutes?, found] at ok
      | some T =>
          cases T <;> simp [Region.checkRoutes?, found, Option.bind_eq_some_iff] at ok
          obtain ⟨ls, hl, rs, hr, rfl⟩ := ok
          have unique := (Tm.synthRouteType?_sound found).2.1
          rename_i A B
          have arms : (if wide then l else ls).HasType (A :: Γ) K ∧
              (if wide then r else rs).HasType (B :: Γ) K := by
            cases wide <;> exact case_types unique typed
          rcases Bool.or_eq_true_iff.mp target with yes | no
          · exact il hl yes arms.1
          · exact ir hr no arms.2
  | let₁ | let₂ | cfg => contradiction

/-- A checked plain transfer fixes its exact target type. -/
theorem plain_target {layout : RouteLayout Empty} {Γ K : List (Ty Empty)} {r s : Region Φ}
    {i : Nat} {A : Ty Empty} (wide : Bool) (ok : r.checkRoutes? layout Γ = some s)
    (target : branchesTo i s = true) (localType : layout[i]? = some (A, none))
    (typed : (if wide then r else s).HasType Γ K) : At K i A := by
  cases wide <;> exact route_target _ ok target localType typed

private theorem local_at {α : Type} {m : Nat} (P : Fin m → α) (L : List α) (i : Fin m) :
    (List.ofFn P ++ L)[i.val]? = some (P i) := by
  simp [List.getElem?_append_left, i.isLt]

/-- A sound seed and transfer rule establish the claim at every bounded anchor. -/
theorem of_worklist {m : Nat} {seed : Fin m → Bool} {edge : Fin m → Fin m → Bool}
    {claim : Fin m → Prop} (initial : ∀ i, seed i = true → claim i)
    (advance : ∀ j i, claim j → edge j i = true → claim i) {depth : Nat} {i : Fin m}
    (hit : i ∈ anchorWorklist seed edge depth) : claim i := by
  induction depth generalizing i with
  | zero => exact initial i (List.mem_filter.mp hit).2
  | succ depth ih =>
      rcases Bool.or_eq_true_iff.mp (List.mem_filter.mp hit).2 with start | step
      · exact initial i start
      · obtain ⟨j, known, next⟩ := List.any_eq_true.mp step
        exact advance j i (ih known) next

theorem aligned_inner {m n : Nat} {keep : Fin m ↪ Fin n} {P S : Fin m → Ty Empty}
    {out : RouteLayout Empty} {K : LCtx (Ty Empty)} {A : Ty Empty} {entry commonEntry : Region Φ} {rows : Fin n → Region Φ}
    {commonRows : Fin m → Region Φ} (wide : Bool)
    (er : entry.checkRoutes? (innerLayout P out) [A] = some commonEntry)
    (rr : ∀ i, (rows (keep i)).checkRoutes? (innerLayout P out) [P i, A] = some (commonRows i))
    (typedEntry : (if wide then entry else commonEntry).HasType [A] (List.ofFn S ++ K))
    (typedRows : ∀ i, (if wide then rows (keep i) else commonRows i).HasType
      [S i, A] (List.ofFn S ++ K))
    {d : Nat} (paths : ∀ i, i ∈ anchored commonEntry commonRows d) : S = P := by
  have entryFixed (i : Fin m) (h : branchesTo i commonEntry = true) : S i = P i :=
    Option.some.inj ((local_at S K i).symm.trans
      (plain_target wide er h (local_at (fun j => (P j, none)) _ i) typedEntry))
  have advance (j i : Fin m) (known : S j = P j) (next : branchesTo i (commonRows j) = true) :
      S i = P i := by
    have typed := typedRows j
    rw [known] at typed
    exact Option.some.inj ((local_at S K i).symm.trans
      (plain_target wide (rr j) next (local_at (fun j => (P j, none)) _ i) typed))
  exact funext fun i => of_worklist entryFixed advance (paths i)

theorem aligned {m n : Nat} {keep : Fin m ↪ Fin n} {P S : Fin m → Ty Empty}
    {L K : LCtx (Ty Empty)} {A : Ty Empty} {entry commonEntry : Region Φ} {rows : Fin n → Region Φ}
    {commonRows : Fin m → Region Φ} (wide : Bool)
    (er : entry.checkRoutes? (layout P L A) [A] = some commonEntry)
    (rr : ∀ i, (rows (keep i)).checkRoutes? (layout P L A) [P i, A] = some (commonRows i))
    (typedEntry : (if wide then entry else commonEntry).HasType [A] (List.ofFn S ++ K))
    (typedRows : ∀ i, (if wide then rows (keep i) else commonRows i).HasType
      [S i, A] (List.ofFn S ++ K))
    {d : Nat} (paths : ∀ i, i ∈ anchored commonEntry commonRows d) : S = P :=
  aligned_inner wide er rr typedEntry typedRows paths

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax
