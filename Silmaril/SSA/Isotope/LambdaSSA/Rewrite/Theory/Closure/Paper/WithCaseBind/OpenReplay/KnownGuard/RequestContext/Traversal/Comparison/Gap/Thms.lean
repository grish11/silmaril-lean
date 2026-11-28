module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Gap.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedGuardComparisonGap

/-! # Strict gap for exact comparison after the selected traversal -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.ComparisonGap

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- Replay the full projection quote as a direct survivor read under the
original request and guard binders. -/
theorem source_eq : selectedEq direct.source quoted.source :=
  SelectedGuardComparisonGap.source_eq

/-- The actual independently selected original packed arrows agree natively. -/
theorem packed_eq : direct.packedSource = quoted.packedSource :=
  SelectedGuardComparisonGap.packed_eq

theorem normalized_ne : direct.normalized ≠ quoted.normalized :=
  SelectedGuardComparisonGap.normalized_ne

/-- Both targets have readbacks. The keys differ because the quote retains
more cases than the direct read. -/
theorem readbacks_ne :
    (AcyclicSyntax.read direct.normalized.val).map Subtype.val ≠
      (AcyclicSyntax.read quoted.normalized.val).map Subtype.val :=
  SelectedGuardComparisonGap.readbacks_ne

/-- Exact comparison reports unknown on this native equality. -/
theorem compare_unknown : direct.compare quoted = .unknown :=
  SelectedGuardComparisonGap.compare_unknown

/-- Replacing just the quote by its direct read suffices for acceptance,
even with the different logical slot widths. -/
theorem contracted_accepted : (direct.compare contracted).accepted = true := rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.ComparisonGap
