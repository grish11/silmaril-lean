module

public import Silmaril.Logic.Smt.Uflia.SExpr.Defs
public import Silmaril.Proofs.Logic.Smt.Uflia.SExprElaboration

/-!
# Accepted QF-UFLIA S-expressions and exact semantic transport

The direct room's sentences include executable decoding evidence, so malformed
input is not a sentence of this room. The semantics is explicitly decoder-based;
this is not an independent proof of correspondence to the SMT-LIB standard.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.SExpr

open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

variable {E : Environment}

/-- Semantics of the actual concrete expression via checked typed decoding. -/
noncomputable def ExpressionHolds (E : Environment) (e : Expr)
    (M : Uflia.Model E.signature) : Prop :=
  ∃ φ, decodeFormula? E e = some φ ∧ M.Holds φ

theorem expressionHolds_iff (a : Assertion E) (M : Uflia.Model E.signature) :
    ExpressionHolds E a.expression M ↔ M.Holds a.formula := by
  simp [ExpressionHolds, a.decoded]

/-- Direct S-expression assertions form an institution over discrete declaration
environments. Signature morphisms transport along equalities only: concrete
symbol-renaming maps and their decoder naturality are separate work. -/
noncomputable def plain : Plain (Disc Environment) where
  Sen E := Assertion E
  map σ a := σ.down ▸ a
  map_id _ _ := rfl
  map_comp σ τ a := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Mod E := Uflia.Model E.signature
  reduct σ M := σ.down.symm ▸ M
  reduct_id _ _ := rfl
  reduct_comp σ τ M := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    rfl
  Sat M a := ExpressionHolds _ a.expression M
  sat_map σ M a := by
    rcases σ with ⟨h⟩
    cases h
    rfl

/-- The raw-environment direct S-expression institution. -/
noncomputable abbrev institution := plain.toInst

/-- A room at an explicit UF environment. Raw environments can be constructed
directly; use `declarationRoom` to retain checked declaration-prefix evidence. -/
noncomputable abbrev room (E : Environment) := plain.room E

/-- Restrict signatures to declaration prefixes that actually decoded. -/
noncomputable def declarationFunctor : Disc DeclarationPrefix ⥤ Room :=
  Disc.functor DeclarationPrefix.environment ⋙ plain.functor

/-- The direct institution whose signatures carry checked declaration-prefix
evidence. This restriction adds no concrete symbol-renaming maps. -/
noncomputable abbrev declarationInstitution :=
  Institution.ofFunctor declarationFunctor

/-- The direct assertion room at a successfully decoded declaration prefix. -/
noncomputable abbrev declarationRoom (checked : DeclarationPrefix) :=
  declarationFunctor.obj checked

/-- The actual typed decoder supplies the forward sentence map. Models are
unchanged, so SAT/UNSAT transport is exact in both directions. -/
noncomputable def decodeCorridor (E : Environment) :
    room E ⟶ Uflia.room E.signature :=
  ⟨Assertion.formula, Disc.functor id, fun M a => (expressionHolds_iff a M).symm⟩

theorem decodeCorridor_modelExpansive (E : Environment) :
    (decodeCorridor E).ModelExpansive := fun M => ⟨M, rfl⟩

/-- A concrete environment supplies its actual typed abstract UF signature.
Equality-only concrete signature maps become identity abstract renamings. -/
def signatureFunctor : Disc Environment ⥤ Signature String where
  obj E := E.signature
  map σ := eqToHom (congrArg Environment.signature σ.down)
  map_id _ := rfl
  map_comp σ τ := by
    rcases σ with ⟨h⟩
    cases h
    rcases τ with ⟨h⟩
    cases h
    simp

/-- Typed decoding is an institution comorphism, not merely a collection of
room-level satisfaction laws. Its model translation is the identity. -/
noncomputable def decodeComorphism :
    Comorphism institution (Uflia.institution String) :=
  Comorphism.ofPlain signatureFunctor (fun _ => Assertion.formula) (fun _ => id)
    (fun _ M a => (expressionHolds_iff a M).symm)
    (fun σ a => by
      rcases σ with ⟨h⟩
      cases h
      exact (Uflia.Term.map_id a.formula).symm)
    (fun σ M => by
      rcases σ with ⟨h⟩
      cases h
      exact (Uflia.Model.reduct_id M).symm)

theorem decodeComorphism_modelExpansive : ∀ S, Silmaril.Logic.Institution.Corridor.ModelExpansive (decodeComorphism.ρ.app S) :=
  fun _ M => ⟨M, rfl⟩

/-- Restrict the actual decoder comorphism to checked declaration prefixes. -/
noncomputable def declarationDecodeComorphism :
    Comorphism declarationInstitution (Uflia.institution String) :=
  Comorphism.ofCorridors
    (Disc.functor DeclarationPrefix.environment ⋙ signatureFunctor)
    (fun checked => decodeCorridor checked.environment)
    (fun σ => by
      rcases σ with ⟨h⟩
      cases h
      change declarationFunctor.map (𝟙 _) ≫ decodeCorridor _ =
        decodeCorridor _ ≫ (Uflia.plain String).functor.map (𝟙 _)
      simp only [Functor.map_id]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)

theorem declarationDecodeComorphism_modelExpansive :
    ∀ S, Silmaril.Logic.Institution.Corridor.ModelExpansive (declarationDecodeComorphism.ρ.app S) := fun _ M => ⟨M, rfl⟩

noncomputable def Assertion.Sat (a : Assertion E) : Prop :=
  ∃ M, ExpressionHolds E a.expression M

noncomputable def Assertion.Unsat (a : Assertion E) : Prop := ¬ a.Sat

theorem Assertion.sat_iff (a : Assertion E) :
    a.Sat ↔ ∃ M : Uflia.Model E.signature, M.Holds a.formula := by
  simp only [Assertion.Sat, expressionHolds_iff]

theorem Assertion.unsat_iff (a : Assertion E) :
    a.Unsat ↔ ¬ ∃ M : Uflia.Model E.signature, M.Holds a.formula :=
  not_congr a.sat_iff

noncomputable def AssertionsHolds (Γ : List (Assertion E)) (M : Uflia.Model E.signature) :
    Prop := ∀ a ∈ Γ, ExpressionHolds E a.expression M

theorem assertionsHolds_iff (Γ : List (Assertion E)) (M : Uflia.Model E.signature) :
    AssertionsHolds Γ M ↔ Uflia.Problem.Holds (Γ.map Assertion.formula) M := by
  simp only [AssertionsHolds, Uflia.Problem.Holds, List.mem_map,
    forall_exists_index, and_imp]
  constructor
  · intro h φ a ha heq
    subst φ
    exact (expressionHolds_iff a M).mp (h a ha)
  · intro h a ha
    exact (expressionHolds_iff a M).mpr (h a.formula a ha rfl)

theorem assertions_sat_iff (Γ : List (Assertion E)) :
    (∃ M, AssertionsHolds Γ M) ↔ Uflia.Problem.Sat (Γ.map Assertion.formula) := by
  simp only [Uflia.Problem.Sat, assertionsHolds_iff]

theorem assertions_unsat_iff (Γ : List (Assertion E)) :
    (¬ ∃ M, AssertionsHolds Γ M) ↔ Uflia.Problem.Unsat (Γ.map Assertion.formula) :=
  not_congr (assertions_sat_iff Γ)

/-! Concrete lexical regression checks do not assume a solver result. -/

example : simpleSymbol "x_12" = true := by decide
example : simpleSymbol "x y" = false := by decide
example : simpleSymbol "|x|" = false := by decide
example : simpleSymbol "_" = false := by decide
example : numeral? (.atom "00") = none := by decide
example : numeral? (.atom "0") = some 0 := by decide
example : (decodeTerm? ({ declarations := [⟨"c", [], .int⟩] } : Environment)
    (.list [.atom "c"])).isNone = true := by decide

end Silmaril.Logic.Smt.Uflia.SExpr
