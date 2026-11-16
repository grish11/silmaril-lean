module

public import Silmaril.Logic.TypeTheory.CIC.Declarations.Lookup.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Projections.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Instantiation.Thms
public import Silmaril.Logic.TypeTheory.CIC.Reduction.Contexts.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.ProjectionCacheLaws

open Silmaril.Logic.TypeTheory.CIC
open Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- A telescope point supplies the selected field and its genuine dependent domain. -/
theorem telescope_field {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {declarations : Context} {T : ValueTelescope.{u}}
    (h : InterpretsTelescope ρ universes globals values declarations T) (xs : T.Points)
    {index : ℕ} {decl : ContextDecl Expr} (hlookup : declarations[index]? = some decl) :
    ∃ value A, (T.arguments xs)[index]? = some value ∧
      Evaluates ρ universes globals (((T.arguments xs).take index).reverse ++ values) decl.type A ∧ value ∈ A := by
  induction h generalizing index with
  | nil => simp at hlookup
  | @assumption values na type declarations A rest htype hrest ih =>
      rcases xs with ⟨x, xs⟩
      cases index with
      | zero =>
          have heq : ({ binder := na, type := type } : ContextDecl Expr) = decl := Option.some.inj hlookup
          cases heq
          exact ⟨x, A, rfl, htype, x.property⟩
      | succ index =>
          obtain ⟨value, B, hvalue, hB, hmember⟩ := ih x xs hlookup
          refine ⟨value, B, hvalue, ?_, hmember⟩
          simpa only [ValueTelescope.arguments, List.take_succ_cons, List.reverse_cons,
            List.append_assoc, List.singleton_append] using hB

/-- Every earlier field projection evaluates to the corresponding actual field. -/
theorem projectionSubstitution_evaluates {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} (reference : InductiveRef) (parameters fields suffix : LocalValues.{u})
    (count : ℕ) (hcount : count ≤ fields.length) :
    List.Forall₂ (Evaluates ρ universes globals (constructorValue 0 (parameters ++ fields) :: suffix))
      (projectionSubstitution reference parameters.length count) (fields.take count).reverse := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
      have hbound : count < fields.length := by omega
      have hlookup : (parameters ++ fields)[parameters.length + count]? = some fields[count] := by
        rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem hbound
      have hhead : Evaluates ρ universes globals (constructorValue 0 (parameters ++ fields) :: suffix)
          (.projection ⟨reference, parameters.length, count⟩ (.rel 0)) fields[count] :=
        .projection (.rel rfl) hlookup
      simpa only [projectionSubstitution, List.take_succ_eq_append_getElem hbound, List.reverse_append,
        List.reverse_singleton, List.singleton_append] using List.Forall₂.cons hhead (ih (by omega))

/-- Smashing a definition-free context preserves its declarations. -/
theorem smash_no_definitions (Γ : Context) (hnone : ∀ d ∈ Γ, d.value = none) (acc : Context) :
    Context.smash acc Γ = acc ++ Γ := by
  induction Γ generalizing acc with
  | nil => simp [Context.smash]
  | cons decl Γ ih =>
      have hd : decl.value = none := hnone decl (by simp)
      have ht : ∀ d ∈ Γ, d.value = none := fun d hm => hnone d (by simp [hm])
      simpa only [Context.smash, hd, List.append_assoc, List.singleton_append] using ih ht (acc ++ [decl])

/-- Realize a checked projection cache with the actual record and parameter
values still in its local context. Source computations can be substituted later. -/
theorem projection_cache_at_record {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values parameters fields arities : LocalValues.{u}}
    {reference : ProjectionRef} {block : MutualInductiveBody} {projection : ProjectionBody}
    {decl : ContextDecl Expr} {ui : List Universe} {A : Value.{u}}
    (hlength : parameters.length = block.parameterCount) (hbound : reference.argument ≤ fields.length)
    (hcache : projection.type =
      (((decl.type.lift 1 reference.argument).subst
        (projectionSubstitution reference.inductiveRef block.parameterCount reference.argument) 0).subst
          (inductiveSubstitution reference.inductiveRef.block block.universes.abstractInstance block.bodies)
          (block.parameterCount + 1)))
    (hfield : Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui))
      ((fields.take reference.argument).reverse ++ parameters.reverse ++ arities ++ values) decl.type A)
    (hmutual : List.Forall₂ (Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) values)
      (inductiveSubstitution reference.inductiveRef.block block.universes.abstractInstance block.bodies) arities)
    : Evaluates ρ universes globals (constructorValue 0 (parameters ++ fields) :: parameters.reverse ++ values)
      (Expr.instantiate ui projection.type) A := by
  let record := constructorValue 0 (parameters ++ fields)
  let previous := (fields.take reference.argument).reverse
  let base := parameters.reverse ++ arities ++ values
  have hprevious : previous.length = reference.argument := by
    simp only [previous, List.length_reverse, List.length_take, Nat.min_eq_left hbound]
  have hraw : Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) (previous ++ base) decl.type A := by
    simpa only [previous, base, List.append_assoc] using hfield
  have hinserted : Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) (previous ++ [record] ++ base)
      (decl.type.lift 1 reference.argument) A := by
    simpa only [List.length_singleton, hprevious] using evaluates_lift [record] hraw previous base rfl
  have hproject : List.Forall₂ (Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) (record :: base))
      (projectionSubstitution reference.inductiveRef block.parameterCount reference.argument) previous := by
    simpa only [hlength, previous] using projectionSubstitution_evaluates
      (ρ := fun level => (instanceSubstitution ui level).eval ρ) (universes := universes)
      (globals := globals.pullbackUniverses (instanceSubstitution ui)) reference.inductiveRef parameters fields base
      reference.argument hbound
  have hprojected : Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) (record :: base)
      ((decl.type.lift 1 reference.argument).subst
        (projectionSubstitution reference.inductiveRef block.parameterCount reference.argument) 0) A := by
    simpa only [List.nil_append, List.length_nil] using evaluates_subst hinserted
      (projectionSubstitution reference.inductiveRef block.parameterCount reference.argument) previous [] (record :: base)
      (by simp only [List.nil_append, List.singleton_append, List.append_assoc]) hproject
  have hglobals : Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) (record :: parameters.reverse ++ values)
      (((decl.type.lift 1 reference.argument).subst
        (projectionSubstitution reference.inductiveRef block.parameterCount reference.argument) 0).subst
          (inductiveSubstitution reference.inductiveRef.block block.universes.abstractInstance block.bodies)
          (block.parameterCount + 1)) A := by
    simpa only [List.length_cons, List.length_reverse, hlength, Nat.add_comm, List.cons_append] using
      evaluates_subst hprojected
        (inductiveSubstitution reference.inductiveRef.block block.universes.abstractInstance block.bodies)
        arities (record :: parameters.reverse) values
        (by simp only [base, List.cons_append, List.append_assoc]) hmutual
  have htype : Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) (record :: parameters.reverse ++ values) projection.type A := by
    simpa only [hcache, List.length_singleton, hprevious, List.length_nil, List.nil_append,
      List.length_cons, List.length_reverse, hlength, Nat.add_comm] using hglobals
  exact evaluates_instantiate ui htype

/-- Evaluate the exact checked cache by actual field, mutual-name and term substitutions. -/
theorem projection_cache_evaluates {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values parameters fields arities : LocalValues.{u}}
    {reference : ProjectionRef} {block : MutualInductiveBody} {projection : ProjectionBody}
    {decl : ContextDecl Expr} {ui : List Universe} {args : List Expr} {scrutinee : Expr} {A : Value.{u}}
    (hlength : parameters.length = block.parameterCount) (hbound : reference.argument ≤ fields.length)
    (hcache : projection.type =
      (((decl.type.lift 1 reference.argument).subst
        (projectionSubstitution reference.inductiveRef block.parameterCount reference.argument) 0).subst
          (inductiveSubstitution reference.inductiveRef.block block.universes.abstractInstance block.bodies)
          (block.parameterCount + 1)))
    (hfield : Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui))
      ((fields.take reference.argument).reverse ++ parameters.reverse ++ arities ++ values) decl.type A)
    (hmutual : List.Forall₂ (Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) values)
      (inductiveSubstitution reference.inductiveRef.block block.universes.abstractInstance block.bodies) arities)
    (hs : Evaluates ρ universes globals values scrutinee (constructorValue 0 (parameters ++ fields)))
    (hargs : List.Forall₂ (Evaluates ρ universes globals values) args parameters) :
    Evaluates ρ universes globals values
      ((Expr.instantiate ui projection.type).subst (scrutinee :: args.reverse) 0) A := by
  let record := constructorValue 0 (parameters ++ fields)
  have hinstantiated := projection_cache_at_record hlength hbound hcache hfield hmutual
  have hreplacements : List.Forall₂ (Evaluates ρ universes globals values)
      (scrutinee :: args.reverse) (record :: parameters.reverse) := .cons hs (List.rel_reverse hargs)
  simpa only [List.nil_append, List.length_nil] using
    evaluates_subst hinstantiated (scrutinee :: args.reverse) (record :: parameters.reverse) [] values rfl hreplacements

section

variable {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values parameters arities : LocalValues.{u}} {reference : ProjectionRef} {block : MutualInductiveBody}
    {constructor : ConstructorBody} {projection : ProjectionBody} {ui : List Universe} {args : List Expr}
    {scrutinee : Expr} (T : ValueTelescope.{u})
    (hparameters : block.parameterCount = reference.parameterCount)
    (hlength : parameters.length = block.parameterCount)
    (hnone : ∀ d ∈ constructor.arguments ++ block.parameters, d.value = none)
    (hfields : InterpretsTelescope (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) (parameters.reverse ++ arities ++ values)
      constructor.arguments.reverse T)
    (hmutual : List.Forall₂ (Evaluates (fun level => (instanceSubstitution ui level).eval ρ) universes
      (globals.pullbackUniverses (instanceSubstitution ui)) values)
      (inductiveSubstitution reference.inductiveRef.block block.universes.abstractInstance block.bodies) arities)
    (hargs : List.Forall₂ (Evaluates ρ universes globals values) args parameters)

include hparameters hlength hnone hfields hmutual hargs

/-- A genuine tuple's selected field inhabits the exact instantiated checked source cache. -/
theorem projection_point
    (hcache : CoreCheckedProjection reference.inductiveRef.block block reference.inductiveRef.index
      constructor reference.argument projection)
    (hbound : reference.argument < constructor.arguments.assumptionCount) (xs : T.Points)
    (hs : Evaluates ρ universes globals values scrutinee (constructorValue 0 (parameters ++ T.arguments xs))) :
    HasValueAt ρ universes globals values (.projection reference scrutinee)
      ((Expr.instantiate ui projection.type).subst (scrutinee :: args.reverse) 0) := by
  obtain ⟨decl, hdecl, _, _, htype⟩ := hcache
  have hfieldnone : ∀ d ∈ constructor.arguments, d.value = none :=
    fun d hd => hnone d (List.mem_append_left _ hd)
  have hfieldlength : constructor.arguments.assumptionCount = constructor.arguments.length :=
    Context.assumptionCount_eq_length hfieldnone
  have hindex : reference.argument < constructor.arguments.length := hfieldlength ▸ hbound
  have hlookup : constructor.arguments.reverse[reference.argument]? = some decl := by
    rw [List.getElem?_reverse hindex]
    have hposition : constructor.arguments.length - (reference.argument + 1) < constructor.arguments.length := by omega
    simpa only [smash_no_definitions _ hnone [], List.nil_append, hfieldlength,
      List.getElem?_append_left hposition, Nat.sub_sub, Nat.add_comm] using hdecl
  obtain ⟨value, A, hvalue, hA, hmember⟩ := telescope_field hfields xs hlookup
  have hvaluelength : (T.arguments xs).length = constructor.arguments.length := by
    simpa only [List.length_reverse] using interpretsTelescope_length hfields xs
  have hactualbound : reference.argument ≤ (T.arguments xs).length := by omega
  have hfieldtype := projection_cache_evaluates hlength hactualbound htype
    (by simpa only [List.append_assoc] using hA) hmutual hs hargs
  have hselected : (parameters ++ T.arguments xs)[reference.parameterCount + reference.argument]? = some value := by
    rw [← hparameters, ← hlength, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact hvalue
  exact ⟨value, A, .projection hs hselected, hfieldtype, hmember⟩

/-- Constructor-layer inversion supplies a genuine dependent tuple; no projected-type interpretation is assumed. -/
theorem constructorLayer_projection_rule {sourceType : Expr} {D : Value.{u}}
    (hcache : CoreCheckedProjection reference.inductiveRef.block block reference.inductiveRef.index
      constructor reference.argument projection)
    (hbound : reference.argument < constructor.arguments.assumptionCount)
    (hsubset : D ⊆ constructorLayer 1 (fun _ => T) parameters)
    (hsource : Evaluates ρ universes globals values sourceType D)
    (hs : HasValueAt ρ universes globals values scrutinee sourceType) :
    HasValueAt ρ universes globals values (.projection reference scrutinee)
      ((Expr.instantiate ui projection.type).subst (scrutinee :: args.reverse) 0) := by
  obtain ⟨value, A, hvalue, hA, hmember⟩ := hs
  have hrecord : value ∈ constructorLayer 1 (fun _ => T) parameters :=
    hsubset (evaluates_deterministic hA hsource ▸ hmember)
  obtain ⟨index, xs, heq⟩ := mem_constructorLayer.mp hrecord
  have hindex : index = (0 : Fin 1) := Subsingleton.elim _ _
  cases hindex
  exact projection_point T hparameters hlength hnone hfields hmutual hargs hcache hbound xs (heq ▸ hvalue)

/-- Actual checked lookup supplies the cache and field bound for both source typing and realization. -/
theorem checked_projection_source_and_value {sig : GlobalContext} {Γ : Context} {body : InductiveBody} {D : Value.{u}}
    (henv : CoreCheckedEnvironment sig.environment)
    (hlookup : sig.environment.lookupProjection reference = some (block, body, constructor, projection))
    (htyped : CoreTyping sig Γ scrutinee (Expr.mkApps (.inductiveType reference.inductiveRef ui) args))
    (hsubset : D ⊆ constructorLayer 1 (fun _ => T) parameters)
    (hsource : Evaluates ρ universes globals values
      (Expr.mkApps (.inductiveType reference.inductiveRef ui) args) D)
    (hs : HasValueAt ρ universes globals values scrutinee
      (Expr.mkApps (.inductiveType reference.inductiveRef ui) args)) :
    CoreTyping sig Γ (.projection reference scrutinee)
        ((Expr.instantiate ui projection.type).subst (scrutinee :: args.reverse) 0) ∧
      HasValueAt ρ universes globals values (.projection reference scrutinee)
        ((Expr.instantiate ui projection.type).subst (scrutinee :: args.reverse) 0) := by
  obtain ⟨previous, hprevious⟩ := CoreCheckedEnvironment.projection_checked henv hlookup
  have harglength : args.length = block.parameterCount := hargs.length_eq.trans hlength
  exact ⟨CoreTyping.projection hlookup hparameters htyped harglength,
    constructorLayer_projection_rule T hparameters hlength hnone hfields hmutual hargs
      hprevious.checked hprevious.argument_bound hsubset hsource hs⟩

end

end Silmaril.Proofs.Logic.TypeTheory.CIC.ProjectionCacheLaws
