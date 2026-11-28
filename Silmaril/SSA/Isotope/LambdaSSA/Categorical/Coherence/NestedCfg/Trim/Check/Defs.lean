module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Defs

/-! # Check a written CFG restriction at a candidate mask -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

/-- The reindexed entry and every original row. Rows remain indexed by their
original positions so the certificate can check transfers from omitted rows. -/
structure CfgRestriction (Φ : Type v) (n : Nat) where
  entry : Region Φ
  rows : Fin n → Region Φ

namespace CfgRestriction

variable {Φ : Type v} {m n : Nat}

/-- The literal written graph recovered by reembedding the compact labels. -/
def source (c : CfgRestriction Φ n) (keep : Fin m ↪ Fin n) : Region Φ :=
  .cfg (c.entry.renameLabels (retainLabelIndex keep)) n
    (fun i => (c.rows i).renameLabels (retainLabelIndex keep))

/-- The graph on the retained labels and the ordered outward suffix. -/
def retained (c : CfgRestriction Φ n) (keep : Fin m ↪ Fin n) : Region Φ :=
  .cfg c.entry m (fun i => c.rows (keep i))

/-- Check the written entry and every written row. Restriction under a nested
CFG lifts the map over the nested local indices. -/
def check? (keep : Fin m ↪ Fin n) (exitCount : Nat) (r : Region Φ) : Option (CfgRestriction Φ n) :=
  match r with
  | .cfg entry size rows =>
      if h : size = n then
        let rows : Fin n → Region Φ := h ▸ rows
        let reindex := retainLabelIndex keep
        (entry.restrictLabels? (m + exitCount) reindex).bind fun entry' =>
        (Region.checkFamily n (fun i => (rows i).restrictLabels? (m + exitCount) reindex)).map
          fun rows' => ⟨entry', rows'⟩
      else none
  | _ => none

/-- Each original transfer reembeds from the smaller bound. -/
structure Valid (c : CfgRestriction Φ n) (keep : Fin m ↪ Fin n) (exitCount : Nat) (r : Region Φ) : Prop where
  source : c.source keep = r
  entryScope : c.entry.LabelsBound (m + exitCount)
  rowScope : ∀ i, (c.rows i).LabelsBound (m + exitCount)

end CfgRestriction

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
