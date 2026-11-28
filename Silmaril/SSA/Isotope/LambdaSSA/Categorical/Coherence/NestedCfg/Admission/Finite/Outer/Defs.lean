module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Admission.Finite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Trim.Check.Defs

/-! # Admit one known-left nested row in a finite written outer table -/

@[expose] public section

universe v

namespace Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Outer

open Semantics.Categorical (CfgRestriction)

variable {Φ : Type v} [HasTy Φ (Ty Empty)] {a k n : Nat}

/-- Check all outer transfers, including those under nested CFG labels.
The chosen outer row can be anywhere in the written table. The resulting
one-row graph must pass the existing finite nested checker. -/
def check? (outerKeep : Fin 1 ↪ Fin (a + 1)) (innerKeep : Fin (k + 1) ↪ Fin (n + 1))
    (types : Fin (k + 1) → Ty Empty) (r : Region Φ) (exitTypes : LCtx (Ty Empty) := exits) :
    Option (CfgRestriction Φ (a + 1)) :=
  (CfgRestriction.check? outerKeep exitTypes.length r).bind fun c =>
    if Finite.compare? innerKeep types (c.retained outerKeep) exitTypes = .certified then some c else none

/-- A failed candidate or any unsupported selected row gives unknown. -/
def compare? (outerKeep : Fin 1 ↪ Fin (a + 1)) (innerKeep : Fin (k + 1) ↪ Fin (n + 1))
    (types : Fin (k + 1) → Ty Empty) (r : Region Φ) (exitTypes : LCtx (Ty Empty) := exits) : Comparison :=
  if (check? outerKeep innerKeep types r exitTypes).isSome then .certified else .unknown

end Silmaril.Isotope.LambdaSSA.NestedAdmission.Finite.Outer
