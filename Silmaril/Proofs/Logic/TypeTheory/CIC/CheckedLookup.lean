module

public import Silmaril.Logic.TypeTheory.CIC.Declarations.Lookup.Defs
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.CheckedLookupLaws

open Silmaril.Logic.TypeTheory.CIC

private theorem declarations_lookup {levels : List String} {constraints : List UniverseConstraint}
    {declarations : List (String × GlobalDeclaration)}
    (h : CoreCheckedDeclarations levels constraints declarations) {name : String} {declaration : GlobalDeclaration}
    (hlookup : (GlobalEnv.mk levels constraints declarations).lookup name = some declaration) :
    ∃ newer previous, declarations = newer ++ (name, declaration) :: previous ∧
      CoreCheckedDeclarations levels constraints previous ∧
      CoreCheckedDeclaration ⟨levels, constraints, previous⟩ name declaration := by
  induction h with
  | nil => simp [GlobalEnv.lookup] at hlookup
  | @cons declarations head entry htail _ hentry ih =>
      by_cases heq : head = name
      · cases heq
        have hdecl : entry = declaration := by simpa [GlobalEnv.lookup] using hlookup
        cases hdecl
        exact ⟨[], declarations, rfl, htail, hentry⟩
      · have hrest : (GlobalEnv.mk levels constraints declarations).lookup name = some declaration := by
          simpa [GlobalEnv.lookup, heq] using hlookup
        obtain ⟨newer, previous, horder, hprevious, hchecked⟩ := ih hrest
        exact ⟨(head, entry) :: newer, previous, congrArg (List.cons (head, entry)) horder, hprevious, hchecked⟩

theorem declaration_checked {env : GlobalEnv} (henv : CoreCheckedEnvironment env)
    {name : String} {declaration : GlobalDeclaration} (hlookup : env.lookup name = some declaration) :
    ∃ previous, CheckedDeclarationLookup env name declaration previous := by
  obtain ⟨newer, previous, horder, hprevious, hchecked⟩ := declarations_lookup henv.2.2.2 hlookup
  refine ⟨previous, ⟨⟨newer, horder⟩, ?_, hchecked⟩⟩
  refine ⟨henv.1, ?_, ?_, hprevious⟩
  · have hlevels : (GlobalContext.mk { env with declarations := previous } 0 []).AllowsLevel =
        (GlobalContext.mk env 0 []).AllowsLevel := by
      funext level
      cases level <;> rfl
    simpa only [GlobalContext.AllowsUniverse, hlevels] using henv.2.1
  · simpa only [GlobalContext.Satisfies] using henv.2.2.1

theorem inductive_checked {env : GlobalEnv} (henv : CoreCheckedEnvironment env)
    {reference : InductiveRef} {block : MutualInductiveBody} {body : InductiveBody}
    (hlookup : env.lookupInductive reference = some (block, body)) :
    ∃ previous, CheckedInductiveLookup env reference block body previous := by
  unfold GlobalEnv.lookupInductive at hlookup
  cases hd : env.lookup reference.block with
  | none => simp [hd] at hlookup
  | some declaration =>
      cases declaration with
      | constant _ => simp [hd] at hlookup
      | inductiveBlock actualBlock =>
          cases hb : actualBlock.bodies[reference.index]? with
          | none => simp [hd, hb] at hlookup
          | some actualBody =>
              have heq : (actualBlock, actualBody) = (block, body) := by simpa [hd, hb] using hlookup
              cases heq
              obtain ⟨previous, hprevious⟩ := declaration_checked henv hd
              exact ⟨previous, hprevious, hb, hprevious.checked.1, hprevious.checked.2⟩

theorem constructor_checked {env : GlobalEnv} (henv : CoreCheckedEnvironment env)
    {reference : InductiveRef} {index : ℕ} {block : MutualInductiveBody} {body : InductiveBody}
    {constructor : ConstructorBody}
    (hlookup : env.lookupConstructor reference index = some (block, body, constructor)) :
    ∃ previous, CheckedConstructorLookup env reference index block body constructor previous := by
  unfold GlobalEnv.lookupConstructor at hlookup
  cases hi : env.lookupInductive reference with
  | none => simp [hi] at hlookup
  | some pair =>
      rcases pair with ⟨actualBlock, actualBody⟩
      cases hc : actualBody.constructors[index]? with
      | none => simp [hi, hc] at hlookup
      | some actualConstructor =>
          have heq : (actualBlock, actualBody, actualConstructor) = (block, body, constructor) := by
            simpa [hi, hc] using hlookup
          cases heq
          obtain ⟨previous, hprevious⟩ := inductive_checked henv hi
          obtain ⟨allSorts, hlength, hconstructors, hvalid⟩ :=
            (hprevious.checked.members reference.index body hprevious.member).constructors
          have hbound := (List.getElem?_eq_some_iff.mp hc).1
          have hsortbound : index < allSorts.length := by omega
          have hsort := List.getElem?_eq_getElem hsortbound
          exact ⟨previous, hprevious, hc, allSorts, allSorts[index], hlength, hsort, hvalid,
            hconstructors index constructor allSorts[index] hc hsort⟩

private theorem projection_lookup_parts {env : GlobalEnv}
    {reference : ProjectionRef} {block : MutualInductiveBody} {body : InductiveBody}
    {constructor : ConstructorBody} {projection : ProjectionBody}
    (hlookup : env.lookupProjection reference = some (block, body, constructor, projection)) :
    env.lookupConstructor reference.inductiveRef 0 = some (block, body, constructor) ∧
      body.projections[reference.argument]? = some projection := by
  unfold GlobalEnv.lookupProjection at hlookup
  cases hc : env.lookupConstructor reference.inductiveRef 0 with
  | none => simp [hc] at hlookup
  | some triple =>
      rcases triple with ⟨actualBlock, actualBody, actualConstructor⟩
      cases hp : actualBody.projections[reference.argument]? with
      | none => simp [hc, hp] at hlookup
      | some actualProjection =>
          have heq : (actualBlock, actualBody, actualConstructor, actualProjection) =
              (block, body, constructor, projection) := by simpa [hc, hp] using hlookup
          cases heq
          exact ⟨rfl, hp⟩

theorem projection_checked {env : GlobalEnv} (henv : CoreCheckedEnvironment env)
    {reference : ProjectionRef} {block : MutualInductiveBody} {body : InductiveBody}
    {constructor : ConstructorBody} {projection : ProjectionBody}
    (hlookup : env.lookupProjection reference = some (block, body, constructor, projection)) :
    ∃ previous, CheckedProjectionLookup env reference block body constructor projection previous := by
  obtain ⟨hc, hp⟩ := projection_lookup_parts hlookup
  obtain ⟨previous, hprevious⟩ := constructor_checked henv hc
  have hchecked : CoreCheckedProjections reference.inductiveRef.block block reference.inductiveRef.index body :=
    (hprevious.block_checked.checked.members reference.inductiveRef.index body hprevious.block_checked.member).projections
  rcases hchecked with hnone | ⟨recordConstructor, hsingleton, hindices, helimination, hcount, hfields⟩
  · have himpossible : ([] : List ProjectionBody)[reference.argument]? = some projection := hnone ▸ hp
    simp at himpossible
  · have heq : recordConstructor = constructor := by
      simpa only [hsingleton, List.getElem?_cons_zero, Option.some.injEq] using hprevious.constructor_lookup
    have hsingle : body.constructors = [constructor] := heq ▸ hsingleton
    have hlength : body.projections.length = constructor.arguments.assumptionCount := heq ▸ hcount
    have hbound : reference.argument < constructor.arguments.assumptionCount :=
      hlength ▸ (List.getElem?_eq_some_iff.mp hp).1
    have hfield : CoreCheckedProjection reference.inductiveRef.block block reference.inductiveRef.index
        constructor reference.argument projection := heq ▸ hfields reference.argument projection hp
    exact ⟨previous, hprevious, hp, hsingle, hindices, helimination, hlength, hbound, hfield⟩

/-- The real checked cache determines the source projection's requested type. -/
theorem projection_field_typed {sig : GlobalContext} (henv : CoreCheckedEnvironment sig.environment)
    {Γ : Context} {reference : ProjectionRef} {scrutinee : Expr} {ui : List Universe} {args : List Expr}
    {block : MutualInductiveBody} {body : InductiveBody} {constructor : ConstructorBody} {projection : ProjectionBody}
    (hlookup : sig.environment.lookupProjection reference = some (block, body, constructor, projection))
    (hparameters : block.parameterCount = reference.parameterCount)
    (hs : CoreTyping sig Γ scrutinee (Expr.mkApps (.inductiveType reference.inductiveRef ui) args))
    (hargs : args.length = block.parameterCount) :
    ∃ previous decl, CheckedProjectionLookup sig.environment reference block body constructor projection previous ∧
      (Context.smash [] (constructor.arguments ++ block.parameters))[
        constructor.arguments.assumptionCount - (reference.argument + 1)]? = some decl ∧
      decl.binder.name = some projection.name ∧ projection.relevance = decl.binder.relevance ∧
      CoreTyping sig Γ (.projection reference scrutinee)
        ((Expr.instantiate ui
          (((decl.type.lift 1 reference.argument).subst
            (projectionSubstitution reference.inductiveRef block.parameterCount reference.argument) 0).subst
              (inductiveSubstitution reference.inductiveRef.block block.universes.abstractInstance block.bodies)
              (block.parameterCount + 1))).subst (scrutinee :: args.reverse) 0) := by
  obtain ⟨previous, hprevious⟩ := projection_checked henv hlookup
  obtain ⟨decl, hdecl, hname, hrelevance, hcache⟩ := hprevious.checked
  refine ⟨previous, decl, hprevious, hdecl, hname, hrelevance, ?_⟩
  simpa only [hcache] using CoreTyping.projection hlookup hparameters hs hargs

end Silmaril.Proofs.Logic.TypeTheory.CIC.CheckedLookupLaws
