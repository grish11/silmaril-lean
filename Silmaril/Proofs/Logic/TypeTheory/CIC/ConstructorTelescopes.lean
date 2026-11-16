module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Defs
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Coherence.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.ConstructorValues.Tags.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.ConstructorTelescopeLaws

open Silmaril.Logic.TypeTheory.CIC
open Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- Actual no-definition replacement variables evaluate to their corresponding local field values. -/
theorem evaluates_extendedSubst {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {Γ : Context} (hnone : ∀ d ∈ Γ, d.value = none) (pre fields suffix : LocalValues.{u}) (hlen : fields.length = Γ.length) :
    List.Forall₂ (Evaluates ρ universes globals (pre ++ fields ++ suffix)) (Γ.extendedSubst pre.length) fields := by
  induction Γ generalizing pre fields with
  | nil =>
      have hf : fields = [] := by simpa using hlen
      subst fields
      exact .nil
  | cons d Γ ih =>
      have hd := hnone d (by simp)
      cases fields with
      | nil => simp at hlen
      | cons a fields =>
          have ht := ih (fun e he => hnone e (by simp only [List.mem_cons]; exact Or.inr he)) (pre ++ [a]) fields (by simpa using hlen)
          simp only [Context.extendedSubst, hd]
          apply List.Forall₂.cons
          · apply Evaluates.rel
            simp only [List.append_assoc, List.cons_append, List.getElem?_append_right (le_refl pre.length), Nat.sub_self, List.getElem?_cons_zero]
          · simpa only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] using ht

/-- Definition-free source arguments are the replacement variables in application order. -/
theorem extendedList_eq_reverse_extendedSubst {Γ : Context}
    (hnone : ∀ d ∈ Γ, d.value = none) (offset : ℕ) :
    Γ.extendedList offset = (Γ.extendedSubst offset).reverse := by
  induction Γ generalizing offset with
  | nil => rfl
  | cons d Γ ih =>
      have hd := hnone d (List.mem_cons_self ..)
      have ht := ih (fun e he => hnone e (List.mem_cons_of_mem _ he)) (offset + 1)
      simpa only [Context.extendedList, Context.extendedSubst, hd, List.reverse_cons] using congrArg (· ++ [.rel offset]) ht

/-- Applying a source constructor to its actual field variables uses every tuple argument exactly once. -/
theorem evaluates_extendedList {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {Γ : Context} (hnone : ∀ d ∈ Γ, d.value = none) (fields suffix : LocalValues.{u}) (hlen : fields.length = Γ.length) :
    List.Forall₂ (Evaluates ρ universes globals (fields.reverse ++ suffix)) (Γ.extendedList 0) fields := by
  have hreverse : fields.reverse.length = Γ.length := by simpa only [List.length_reverse] using hlen
  have hvariables := evaluates_extendedSubst (ρ := ρ) (universes := universes) (globals := globals) hnone [] fields.reverse suffix hreverse
  simpa only [List.nil_append, List.length_nil, ← extendedList_eq_reverse_extendedSubst hnone, List.reverse_reverse] using List.rel_reverse hvariables

/-- A full telescope trace inhabits the genuine iterated dependent product. -/
theorem telescope_trace_mem (T : ValueTelescope.{u}) (B f : T.Points → Value.{u})
    (h : ∀ xs, f xs ∈ B xs) : T.trace f ∈ T.pi B := by
  induction T with
  | nil => exact h PUnit.unit
  | bind A rest ih => exact tracePi_intro _ (fun x => ih x _ _ (fun xs => h ⟨x, xs⟩))

/-- Tuple inversion is exact and retains the actual constructor tag, parameters and dependent fields. -/
theorem mem_constructorLayer {count : ℕ} {telescopes : Fin count → ValueTelescope.{u}}
    {parameters : LocalValues.{u}} {value : Value.{u}} :
    value ∈ constructorLayer count telescopes parameters ↔
      ∃ (index : Fin count) (xs : (telescopes index).Points),
        value = constructorValue index.val (parameters ++ (telescopes index).arguments xs) := by
  constructor
  · intro h
    obtain ⟨⟨index, xs⟩, heq⟩ := ZFSet.mem_range.mp h
    exact ⟨index, xs, heq.symm⟩
  · rintro ⟨index, xs, heq⟩
    exact ZFSet.mem_range.mpr ⟨⟨index, xs⟩, heq.symm⟩

/-- Each constructed constructor trace lands in the actual finite tagged layer. -/
theorem constructor_trace_mem {count : ℕ} (telescopes : Fin count → ValueTelescope.{u})
    (parameters : LocalValues.{u}) (index : Fin count) :
    (telescopes index).trace (fun xs => constructorValue index.val (parameters ++ (telescopes index).arguments xs)) ∈
      (telescopes index).pi (fun _ => constructorLayer count telescopes parameters) :=
  telescope_trace_mem _ _ _ (fun xs => mem_constructorLayer.mpr ⟨index, xs, rfl⟩)

/-- An actual tuple has exactly the number of declarations in its interpreted source telescope. -/
theorem interpretsTelescope_length {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {declarations : Context} {T : ValueTelescope.{u}}
    (h : InterpretsTelescope ρ universes globals values declarations T) (xs : T.Points) :
    (T.arguments xs).length = declarations.length := by
  induction h with
  | nil => rfl
  | assumption htype hrest ih =>
      rcases xs with ⟨x, xs⟩
      exact congrArg Nat.succ (ih x xs)

/-- Actual evaluation of the same source fields determines the complete dependent telescope. -/
theorem interpretsTelescope_unique {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {declarations : Context} {T other : ValueTelescope.{u}}
    (h : InterpretsTelescope ρ universes globals values declarations T)
    (hother : InterpretsTelescope ρ universes globals values declarations other) : T = other := by
  induction h generalizing other with
  | nil => cases hother; rfl
  | @assumption values na type declarations A rest htype hrest ih =>
      cases hother with
      | @assumption _ _ _ _ A' rest' htype' hrest' =>
          have hdomain : A = A' := evaluates_deterministic htype htype'
          cases hdomain
          have htail : rest = rest' := funext fun x => ih x (hrest' x)
          cases htail
          rfl

/-- Actual field tuples realize their full source branch context, in the genuine de Bruijn order. -/
theorem interpretsTelescope_context {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {declarations Γ : Context} {T : ValueTelescope.{u}}
    (h : InterpretsTelescope ρ universes globals values declarations T)
    (hΓ : InterpretsLocal ρ universes globals Γ values) (xs : T.Points) :
    InterpretsLocal ρ universes globals (declarations.reverse ++ Γ) ((T.arguments xs).reverse ++ values) := by
  induction h generalizing Γ with
  | nil => exact hΓ
  | @assumption values na type declarations A rest htype hrest ih =>
      rcases xs with ⟨x, xs⟩
      have hx : InterpretsLocal ρ universes globals ({ binder := na, type := type } :: Γ) ((x : Value.{u}) :: values) :=
        InterpretsLocal.assumption hΓ htype x.property
      simpa only [ValueTelescope.arguments, List.reverse_cons, List.append_assoc, List.singleton_append] using ih x hx xs

/-- Source declaration abstraction evaluates to the actual dependent telescope product. -/
theorem evaluates_telescope_products {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {declarations : Context} {T : ValueTelescope.{u}} {result : Expr}
    (h : InterpretsTelescope ρ universes globals values declarations T) (B : T.Points → Value.{u})
    (hresult : ∀ xs, Evaluates ρ universes globals ((T.arguments xs).reverse ++ values) result (B xs)) :
    Evaluates ρ universes globals values (Context.abstractProducts declarations.reverse result) (T.pi B) := by
  induction h with
  | nil => exact hresult PUnit.unit
  | @assumption values na type declarations A rest htype hrest ih =>
      simp only [List.reverse_cons, Context.abstractProducts, List.foldl_append, List.foldl_cons, List.foldl_nil]
      apply Evaluates.product htype
      intro x
      apply ih x (fun xs => B ⟨x, xs⟩)
      intro xs
      simpa only [ValueTelescope.arguments, List.reverse_cons, List.append_assoc, List.singleton_append] using hresult ⟨x, xs⟩

/-- Actual source lambda abstraction realizes any interpreted dependent constructor body. -/
theorem evaluates_telescope_lambdas {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {declarations : Context} {T : ValueTelescope.{u}} {body : Expr}
    (h : InterpretsTelescope ρ universes globals values declarations T) (f : T.Points → Value.{u})
    (hbody : ∀ xs, Evaluates ρ universes globals ((T.arguments xs).reverse ++ values) body (f xs)) :
    Evaluates ρ universes globals values (Context.abstractLambdas declarations.reverse body) (T.trace f) := by
  induction h with
  | nil => exact hbody PUnit.unit
  | @assumption values na type declarations A rest htype hrest ih =>
      simp only [List.reverse_cons, Context.abstractLambdas, List.foldl_append, List.foldl_cons, List.foldl_nil]
      apply Evaluates.lambda htype
      intro x
      apply ih x (fun xs => f ⟨x, xs⟩)
      intro xs
      simpa only [ValueTelescope.arguments, List.reverse_cons, List.append_assoc, List.singleton_append] using hbody ⟨x, xs⟩

/-- Source application of every actual field realizes exactly the selected telescope function value. -/
theorem evaluates_telescope_application {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} (T : ValueTelescope.{u}) (f : T.Points → Value.{u}) (xs : T.Points)
    {function : Expr} {arguments : List Expr}
    (hfunction : Evaluates ρ universes globals values function (T.trace f))
    (harguments : List.Forall₂ (Evaluates ρ universes globals values) arguments (T.arguments xs)) :
    Evaluates ρ universes globals values (Expr.mkApps function arguments) (f xs) := by
  induction T generalizing function arguments with
  | nil =>
      cases harguments
      cases xs
      exact hfunction
  | bind A rest ih =>
      rcases xs with ⟨x, xs⟩
      cases harguments with
      | cons ha hargs =>
          have happ := Evaluates.application hfunction ha
          rw [ValueTelescope.trace, trace_beta A _ x] at happ
          exact ih x (fun xs => f ⟨x, xs⟩) xs (function := .app function _) happ hargs

/-- An explicitly assigned constructor realizes its actual declared type in the constructed layer. -/
theorem constructorLayer_constructor_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {reference : InductiveRef} {ui : List Universe}
    {block : MutualInductiveBody} {constructor : ConstructorBody} {count : ℕ}
    (telescopes : Fin count → ValueTelescope.{u}) (index : Fin count)
    (hlookup : globals.constructor reference index.val ui =
      some ((telescopes index).trace (fun xs => constructorValue index.val ((telescopes index).arguments xs))))
    (htype : Evaluates ρ universes globals values (constructorType reference ui block constructor)
      ((telescopes index).pi (fun _ => constructorLayer count telescopes []))) :
    HasValueAt ρ universes globals values (.constructor reference index.val ui) (constructorType reference ui block constructor) := by
  refine ⟨_, _, Evaluates.constructor hlookup, htype, ?_⟩
  simpa only [List.nil_append] using constructor_trace_mem telescopes [] index

/-- An actual interpreted constructor applied to its dependent source arguments produces its exact tag and fields. -/
theorem constructorLayer_application {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values parameters : LocalValues.{u}} {function type : Expr} {arguments : List Expr}
    {count : ℕ} (telescopes : Fin count → ValueTelescope.{u}) (index : Fin count)
    (xs : (telescopes index).Points)
    (hfunction : Evaluates ρ universes globals values function
      ((telescopes index).trace (fun ys => constructorValue index.val (parameters ++ (telescopes index).arguments ys))))
    (harguments : List.Forall₂ (Evaluates ρ universes globals values) arguments ((telescopes index).arguments xs))
    (htype : Evaluates ρ universes globals values type (constructorLayer count telescopes parameters)) :
    HasValueAt ρ universes globals values (Expr.mkApps function arguments) type :=
  ⟨_, _, evaluates_telescope_application _ _ xs hfunction harguments, htype,
    mem_constructorLayer.mpr ⟨index, xs, rfl⟩⟩

end Silmaril.Proofs.Logic.TypeTheory.CIC.ConstructorTelescopeLaws
