module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Mixed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgFiniteSyntax
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Thms

/-! # Exact typing constraints from mixed written transfers -/

public section

universe v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMixedSyntax

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Mixed

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

theorem valid {q o k n : Nat} {outerKeep : Fin (q + 1) ↪ Fin (o + 1)}
    {innerKeep : Fin (k + 1) ↪ Fin (n + 1)} {P : Fin (k + 1) → Ty Empty} {Q : Fin q → Ty Empty}
    {r : Region Φ} {L : LCtx (Ty Empty)} {p : Plan Φ q (o + 1) (k + 1) (n + 1)}
    (ok : check? outerKeep innerKeep P Q r L = some p) : p.Valid outerKeep innerKeep P Q r L := by
  simp only [check?, Option.bind_eq_some_iff] at ok
  obtain ⟨outer, ho, inner, hi, rows, hr, ok⟩ := ok
  split at ok <;> try contradiction
  rename_i all
  cases Option.some.inj ok
  exact ⟨CfgRestriction.check?_sound ho, NestedAdmission.Finite.check?_sound hi, Region.checkFamily_some hr,
    fun i => by simpa using List.all_eq_true.mp all i (List.mem_finRange _)⟩

theorem shell_endpoints {q o k n : Nat} {outerKeep : Fin (q + 1) ↪ Fin (o + 1)}
    {innerKeep : Fin (k + 1) ↪ Fin (n + 1)} {P : Fin (k + 1) → Ty Empty} {Q : Fin q → Ty Empty}
    {r : Region Φ} {L : LCtx (Ty Empty)} {p : Plan Φ q (o + 1) (k + 1) (n + 1)}
    (ok : p.Valid outerKeep innerKeep P Q r L) :
    p.outer.entry = .br 0 (.inl p.inner.initializer) ∧ p.outer.rows (outerKeep 0) = p.inner.outer := by
  obtain ⟨entry, _, rows⟩ := Region.cfg.inj ok.inner.root
  exact ⟨entry, congrFun (eq_of_heq rows) (0 : Fin 1)⟩

private theorem exit_at {α : Type} {m i : Nat} (P : Fin m → α) (K : List α) :
    (List.ofFn P ++ K)[m + i]? = K[i]? := by
  rw [List.getElem?_append_right (by simp), List.length_ofFn, Nat.add_sub_cancel_left]

private theorem local_at {α : Type} {m : Nat} (P : Fin m → α) (K : List α) (i : Fin m) :
    (List.ofFn P ++ K)[i.val]? = some (P i) := by
  simp [List.getElem?_append_left, i.isLt]

private theorem ordinary_at {q : Nat} (A : Ty Empty) (Q : Fin q → Ty Empty) (L : LCtx (Ty Empty))
    (i : Fin q) : (layout A (List.ofFn Q ++ L))[i.succ.val]? = some (Q i, none) := by
  simp only [layout, Fin.val_succ, List.getElem?_cons_succ, List.getElem?_map,
    local_at Q L i, Option.map_some]

theorem nested_type {q o k n : Nat} {outerKeep : Fin (q + 1) ↪ Fin (o + 1)}
    {innerKeep : Fin (k + 1) ↪ Fin (n + 1)} {P : Fin (k + 1) → Ty Empty} {Q : Fin q → Ty Empty}
    {r : Region Φ} {L K : LCtx (Ty Empty)} {p : Plan Φ q (o + 1) (k + 1) (n + 1)}
    (ok : p.Valid outerKeep innerKeep P Q r L)
    (entry : p.inner.entry.HasType [p.inner.payload] (List.ofFn P ++ K))
    (rows : ∀ j, (p.inner.rows (innerKeep j)).HasType [P j, p.inner.payload] (List.ofFn P ++ K))
    (i : Fin q) (hit : p.nestedAnchor i = true) : At K i.succ (Q i) := by
  have target : (NestedAdmission.Finite.layout P (List.ofFn Q ++ L) p.inner.payload)[k + 1 + i.succ.val]? =
      some (Q i, none) := by
    unfold NestedAdmission.Finite.layout
    rw [exit_at]
    simp only [Fin.val_succ, List.getElem?_cons_succ, List.getElem?_map, local_at Q L i, Option.map_some]
  have fixed : At (List.ofFn P ++ K) (k + 1 + i.succ.val) (Q i) := by
    rcases Bool.or_eq_true_iff.mp hit with viaEntry | viaRow
    · exact NestedCfgFiniteSyntax.plain_target true ok.inner.entryRoute viaEntry target entry
    · obtain ⟨j, _, edge⟩ := List.any_eq_true.mp viaRow
      exact NestedCfgFiniteSyntax.plain_target true (ok.inner.rowRoutes j) edge target (rows j)
  change (List.ofFn P ++ K)[k + 1 + i.succ.val]? = some (Q i) at fixed
  rwa [exit_at] at fixed

theorem ordinary_types {q o k n : Nat} {outerKeep : Fin (q + 1) ↪ Fin (o + 1)}
    {innerKeep : Fin (k + 1) ↪ Fin (n + 1)} {P : Fin (k + 1) → Ty Empty} {Q : Fin q → Ty Empty}
    {r : Region Φ} {L : LCtx (Ty Empty)} {p : Plan Φ q (o + 1) (k + 1) (n + 1)}
    (ok : p.Valid outerKeep innerKeep P Q r L) {S : Fin (q + 1) → Ty Empty}
    (seed : ∀ i, p.nestedAnchor i = true → At (List.ofFn S ++ L) i.succ (Q i))
    (rows : ∀ j : Fin q, (p.outer.rows (outerKeep j.succ)).HasType [S j.succ] (List.ofFn S ++ L)) :
    ∀ i : Fin q, S i.succ = Q i := by
  have initial (i : Fin q) (hit : p.nestedAnchor i = true) : S i.succ = Q i :=
    Option.some.inj ((local_at S L i.succ).symm.trans (seed i hit))
  have advance (j i : Fin q) (known : S j.succ = Q j)
      (edge : NestedAdmission.Finite.branchesTo i.succ.val (p.commonOrdinary j) = true) : S i.succ = Q i := by
    have typed := rows j
    rw [known] at typed
    exact Option.some.inj ((local_at S L i.succ).symm.trans
      (NestedCfgFiniteSyntax.plain_target true (ok.ordinaryRoutes j) edge
        (ordinary_at p.inner.payload Q L i) typed))
  exact fun i => NestedCfgFiniteSyntax.of_worklist initial advance (ok.anchors i)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgMixedSyntax
