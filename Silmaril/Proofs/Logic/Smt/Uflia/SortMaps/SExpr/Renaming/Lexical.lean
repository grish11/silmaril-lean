module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Core.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Normalization.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic
open Uflia.SExpr
namespace Fixed
export Uflia.SExpr.Renaming (SyntaxLocals syntaxLocal? syntaxBindings? normalizeFuel? normalize?
  LegalLocals legalLocals_append letBindings_legal normalizeApplication_eq normalizeAtom_eq
  decodeAtom_eq decodeAtomUF decodeApplicationUF lookup_lexical lookup_not_numeral
  normalizeMapM_transport)
end Fixed
open Fixed
variable {E F : Environment}

@[simp] theorem fixed_mapPacked_id (t : PackedTerm F) :
    Uflia.SExpr.Renaming.mapPacked (𝟙 F.signature) t = t := by
  cases t
  simp [Uflia.SExpr.Renaming.mapPacked, Uflia.Term.map_id]

def mapLocals (f : environmentSignature E ⟶ environmentSignature F) (locals : Locals E) :
    Locals F := locals.map (fun entry => (entry.1, mapPacked f entry.2))

/-- Reuse the established lexical relation in the target environment. -/
def LocalsRelated (f : environmentSignature E ⟶ environmentSignature F)
    (locals : Locals E) (syntaxLocals : SyntaxLocals) : Prop :=
  Uflia.SExpr.Renaming.LocalsRelated (𝟙 F.signature) (mapLocals f locals) syntaxLocals

@[simp] theorem local_mapLocals (f : environmentSignature E ⟶ environmentSignature F)
    (locals : Locals E) (name : String) :
    local? (mapLocals f locals) name = (local? locals name).map (mapPacked f) := by
  induction locals with
  | nil => rfl
  | cons entry locals ih =>
    rcases entry with ⟨key, value⟩
    simp only [mapLocals, List.map_cons, local?]
    split <;> simp_all [mapLocals]

theorem localsRelated_lookup (f : environmentSignature E ⟶ environmentSignature F)
    {locals : Locals E} {syntaxLocals : SyntaxLocals}
    (h : LocalsRelated f locals syntaxLocals) (name : String) :
    match local? locals name, syntaxLocal? syntaxLocals name with
    | none, none => True
    | some value, some output =>
        decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value)
    | _, _ => False := by
  have related := Uflia.SExpr.Renaming.localsRelated_lookup (𝟙 F.signature) h name
  rw [local_mapLocals] at related
  cases hs : local? locals name <;> cases ht : syntaxLocal? syntaxLocals name <;>
    simp_all

theorem localsRelated_absent (f : environmentSignature E ⟶ environmentSignature F)
    {locals : Locals E} {syntaxLocals : SyntaxLocals}
    (h : LocalsRelated f locals syntaxLocals) (name : String)
    (absent : local? locals name = none) : syntaxLocal? syntaxLocals name = none := by
  have related := localsRelated_lookup f h name
  cases ht : syntaxLocal? syntaxLocals name <;> simp_all

theorem localsRelated_append (f : environmentSignature E ⟶ environmentSignature F)
    {xs ys : Locals E} {ss ts : SyntaxLocals}
    (left : LocalsRelated f xs ss) (right : LocalsRelated f ys ts) :
    LocalsRelated f (xs ++ ys) (ss ++ ts) := by
  unfold LocalsRelated mapLocals
  rw [List.map_append]
  exact Uflia.SExpr.Renaming.localsRelated_append _ left right

/-- Mapping typed lexical values preserves all duplicate-name checks. -/
theorem mapLocals_anyName (f : environmentSignature E ⟶ environmentSignature F)
    (locals : Locals E) (name : String) :
    (mapLocals f locals).any (fun entry => entry.1 == name) =
      locals.any (fun entry => entry.1 == name) := by
  simp only [mapLocals, List.any_map, Function.comp_def]

/-- Forward transport of checked parallel bindings; RHS scopes are unchanged. -/
theorem letBindings_map (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (es : List Expr) (values : Locals E)
    (h : letBindings? source es = some values) :
    letBindings? (fun e => (source e).map (mapPacked f)) es = some (mapLocals f values) := by
  induction es generalizing values with
  | nil =>
    have hv : ([] : Locals E) = values := Option.some.inj h
    subst values
    rfl
  | cons e es ih =>
    unfold letBindings? at h
    split at h
    · contradiction
    · rename_i ignored name rhs tail hshape
      obtain ⟨he, htail⟩ : e = .list [.atom name, rhs] ∧ es = tail := List.cons.inj hshape
      subst e
      subst tail
      split at h
      · contradiction
      · rename_i valid
        obtain ⟨value, hv, rest⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨vs, hvs, last⟩ := Option.bind_eq_some_iff.mp rest
        split at last
        · contradiction
        · rename_i nodup
          have equality : (name, value) :: vs = values := Option.some.inj last
          subst values
          simp_all [letBindings?, mapLocals, List.any_map, Function.comp_def]
    · contradiction

/-- Existing parallel-let normalization applies after mapping typed values. -/
theorem normalizeLetBindings_transport (f : environmentSignature E ⟶ environmentSignature F)
    (source : Expr → Option (PackedTerm E)) (normalize : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      normalize e = some output ∧
      decodeTermFuel? F (expressionFuel output) output = some (mapPacked f value))
    (es : List Expr) (values : Locals E) (h : letBindings? source es = some values) :
    ∃ outputs, syntaxBindings? normalize es = some outputs ∧ LocalsRelated f values outputs := by
  apply Uflia.SExpr.Renaming.normalizeLetBindings_transport (𝟙 F.signature)
    (fun e => (source e).map (mapPacked f)) normalize ?_ es (mapLocals f values)
    (letBindings_map f source es values h)
  intro e mapped hm
  cases hv : source e with
  | none => simp [hv] at hm
  | some value =>
    have heq : mapPacked f value = mapped := by simpa [hv] using hm
    subst mapped
    obtain ⟨output, hn, hd⟩ := children e value hv
    exact ⟨output, hn, by simpa using hd⟩

end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
