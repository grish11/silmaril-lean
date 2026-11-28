module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Check.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Thms

/-! # Read exact nested admission evidence from a successful traversal -/

public section

universe v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmissionSyntax

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.NestedAdmission

variable {Φ : Type v} [HasTy Φ (Ty Empty)]

omit [HasTy Φ (Ty Empty)] in
theorem selected_tag {tag : CaseTag} {r s : Region Φ} (ok : selectTag? tag r = some s) :
    Region.PruneConstructorTests (r.substVars (Tm.replaceNewest (tag.inject (.var 0)))) s := by
  cases r with
  | case a l r =>
      cases a <;> try contradiction
      rename_i i
      cases i with
      | zero =>
          cases Option.some.inj ok
          cases tag
          · exact .inl (.keep _)
          · exact .inr (.keep _)
      | succ => contradiction
  | br | let₁ | let₂ | cfg => contradiction

omit [HasTy Φ (Ty Empty)] in
theorem selected {r s : Region Φ} (ok : selectLeft? r = some s) :
    Region.PruneConstructorTests (r.substVars (Tm.replaceNewest (.inl (.var 0)))) s :=
  selected_tag (tag := .inl) ok

omit [HasTy Φ (Ty Empty)] in
private theorem entry_tag {r : Region Φ} {tag : Bool} (ok : innerTag? r = some tag) :
    r = innerEntry tag := by
  cases r with
  | br i a =>
      cases i with
      | succ => contradiction
      | zero =>
          cases a with
          | var j =>
              cases j with
              | zero => cases Option.some.inj ok; rfl
              | succ => contradiction
          | inl a =>
              cases a <;> try contradiction
              rename_i j
              cases j with
              | zero => cases Option.some.inj ok; rfl
              | succ => contradiction
          | op | let₁ | pair | unit | let₂ | inr | case | abort => contradiction
  | case | let₁ | let₂ | cfg => contradiction

omit [HasTy Φ (Ty Empty)] in
private theorem selected_row {r s : Region Φ} {tag : Bool}
    (ok : (if tag then selectLeft? r else some r) = some s) :
    if tag then Region.PruneConstructorTests (r.substVars (Tm.replaceNewest (.inl (.var 0)))) s else r = s := by
  cases tag
  · exact Option.some.inj ok
  · exact selected ok

theorem valid {r : Region Φ} {p : Plan Φ} (ok : check? r = some p) : p.Valid r := by
  simp only [check?] at ok
  split at ok <;> try contradiction
  rename_i blocks
  simp only [Option.bind_eq_some_iff] at ok
  obtain ⟨chosen, outer, ok⟩ := ok
  split at ok <;> try contradiction
  rename_i entry rows
  simp only [Option.bind_eq_some_iff] at ok
  obtain ⟨compact, he, sparse, hb, ok⟩ := ok
  cases ht : innerTag? compact with
  | none => simp [ht] at ok
  | some tag =>
      simp only [ht, Option.bind_eq_some_iff, Option.some.injEq] at ok
      obtain ⟨body, hbody, common, hcommon, rfl⟩ := ok
      obtain ⟨entryScope, restoreEntry⟩ := Region.restrictLabels?_sound he
      have rowReadback := fun i => Region.restrictLabels?_sound (Region.checkFamily_some hb i)
      have restoreRows := funext (fun i => (rowReadback i).2)
      refine ⟨?_, ?_, entry_tag ht, entryScope, fun i => (rowReadback i).1,
        selected_row hbody, Region.checkRoutes?_sound hcommon⟩
      · congr 1
        funext i
        cases Subsingleton.elim i (0 : Fin 1)
        rfl
      · rw [restoreEntry, restoreRows]
        exact selected outer

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgAdmissionSyntax
