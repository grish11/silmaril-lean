module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Defs
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.SetSemanticsLaws

open Silmaril.Logic.TypeTheory.CIC.SetSemantics
open Silmaril.Logic.TypeTheory.CIC

universe u

theorem mem_traceLambda {A : Value.{u}} {f : A → Value.{u}} {z : Value.{u}} :
    z ∈ traceLambda A f ↔ ∃ x : A, ∃ y ∈ f x, z = ZFSet.pair x y := by
  simp [traceLambda, eq_comm]

theorem mem_traceApply {f x y : Value.{u}} : y ∈ traceApply f x ↔ ZFSet.pair x y ∈ f := by
  constructor
  · intro h
    exact (ZFSet.mem_sep.mp h).2
  · intro h
    apply ZFSet.mem_sep.mpr
    refine ⟨?_, h⟩
    apply ZFSet.mem_sUnion.mpr
    refine ⟨{x, y}, ?_, by simp⟩
    apply ZFSet.mem_sUnion.mpr
    exact ⟨ZFSet.pair x y, h, by simp [ZFSet.pair]⟩

/-- Beta is proved only at an actual member of the function's semantic domain. -/
theorem trace_beta (A : Value.{u}) (f : A → Value.{u}) (x : A) :
    traceApply (traceLambda A f) x = f x := by
  apply ZFSet.ext
  intro y
  rw [mem_traceApply, mem_traceLambda]
  constructor
  · rintro ⟨x', y', hy', heq⟩
    obtain ⟨hx, hy⟩ := ZFSet.pair_inj.mp heq
    have hxx : x = x' := Subtype.ext hx
    simpa only [hxx, hy] using hy'
  · intro hy
    exact ⟨x, y, hy, rfl⟩

theorem mem_tracePi {A : Value.{u}} {B : A → Value.{u}} {v : Value.{u}} :
    v ∈ tracePi A B ↔ ∃ f : A → Value.{u}, (∀ x, f x ∈ B x) ∧ v = traceLambda A f := by
  rw [tracePi, ZFSet.mem_range]
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨fun x => (f x : Value.{u}), fun x => (f x).property, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun x => ⟨f x, hf x⟩, rfl⟩

theorem tracePi_intro {A : Value.{u}} {B : A → Value.{u}} (f : A → Value.{u}) (hf : ∀ x, f x ∈ B x) :
    traceLambda A f ∈ tracePi A B := mem_tracePi.mpr ⟨f, hf, rfl⟩

theorem tracePi_elim {A : Value.{u}} {B : A → Value.{u}} {v : Value.{u}}
    (hv : v ∈ tracePi A B) (x : A) : traceApply v x ∈ B x := by
  obtain ⟨f, hf, rfl⟩ := mem_tracePi.mp hv
  rw [trace_beta]
  exact hf x

theorem traceLambda_empty {A : Value.{u}} {f : A → Value.{u}} (hf : ∀ x, f x = ∅) :
    traceLambda A f = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [mem_traceLambda, ZFSet.notMem_empty, iff_false, not_exists, not_and]
  intro x y hy
  rw [hf x] at hy
  exact (ZFSet.notMem_empty y hy).elim

theorem mem_truth {P : Prop} {v : Value.{u}} : v ∈ truth P ↔ P ∧ v = ∅ := by
  classical
  by_cases hP : P <;> simp [truth, hP]

theorem truth_subset (P : Prop) : truth P ⊆ ({∅} : Value.{u}) := by
  intro v hv
  exact ZFSet.mem_singleton.mpr (mem_truth.mp hv).2

theorem truth_in_propositionUniverse (P : Prop) : truth P ∈ (propositionUniverse : Value.{u}) :=
  ZFSet.mem_powerset.mpr (truth_subset P)

/-- The dependent product of truth-value codomains is itself exactly a truth-value set. -/
theorem tracePi_truth {A : Value.{u}} {B : A → Value.{u}}
    (hB : ∀ x, B x ⊆ ({∅} : Value.{u})) :
    tracePi A B = truth (∀ x, (∅ : Value.{u}) ∈ B x) := by
  apply ZFSet.ext
  intro v
  rw [mem_truth]
  constructor
  · intro hv
    obtain ⟨f, hf, hv⟩ := mem_tracePi.mp hv
    have hempty : ∀ x, f x = ∅ := fun x => ZFSet.mem_singleton.mp (hB x (hf x))
    have hall : ∀ x, (∅ : Value.{u}) ∈ B x := by
      intro x
      simpa only [hempty x] using hf x
    exact ⟨hall, hv.trans (traceLambda_empty hempty)⟩
  · rintro ⟨hall, rfl⟩
    have hlambda : traceLambda A (fun _ => (∅ : Value.{u})) = ∅ := traceLambda_empty (fun _ => rfl)
    simpa only [hlambda] using tracePi_intro (fun _ => (∅ : Value.{u})) hall

/-- Impredicativity holds over every set-sized domain, with no universe bound on that domain here. -/
theorem tracePi_propositionUniverse {A : Value.{u}} {B : A → Value.{u}}
    (hB : ∀ x, B x ∈ (propositionUniverse : Value.{u})) : tracePi A B ∈ (propositionUniverse : Value.{u}) := by
  have hsubset : ∀ x, B x ⊆ ({∅} : Value.{u}) := fun x => ZFSet.mem_powerset.mp (hB x)
  rw [tracePi_truth hsubset]
  exact truth_in_propositionUniverse _

theorem sort_super {count : ℕ} (ρ : LevelName → ℕ) (universes : UniverseSets.{u} count) (s : SortExpr LevelName)
    (hbudget : s.super.UsesBelow ρ count) :
    sortValue ρ universes.level s ∈ sortValue ρ universes.level s.super := by
  cases s with
  | prop => exact universes.proposition_sort hbudget
  | sprop => exact universes.proposition_sort hbudget
  | type level => exact universes.successor (level.eval ρ) hbudget

theorem sort_cumul {count : ℕ} (ρ : LevelName → ℕ) (universes : UniverseSets.{u} count)
    {a b : SortExpr LevelName} (ha : a.UsesBelow ρ count) (hb : b.UsesBelow ρ count)
    (h : a.Cumul ρ b) : sortValue ρ universes.level a ⊆ sortValue ρ universes.level b := by
  cases a <;> cases b
  all_goals first
    | exact fun _ hv => hv
    | exact universes.proposition_codes _ hb
    | exact universes.cumulative _ _ ha hb h
    | exact h.elim

theorem sort_product {count : ℕ} (ρ : LevelName → ℕ) (universes : UniverseSets.{u} count)
    {a b : SortExpr LevelName} {A : Value.{u}} {B : A → Value.{u}}
    (ha : a.UsesBelow ρ count) (hb : b.UsesBelow ρ count)
    (hA : A ∈ sortValue ρ universes.level a) (hB : ∀ x, B x ∈ sortValue ρ universes.level b) :
    tracePi A B ∈ sortValue ρ universes.level (a.product b) := by
  cases b with
  | prop => exact tracePi_propositionUniverse hB
  | sprop => exact tracePi_propositionUniverse hB
  | type range =>
      cases a with
      | prop =>
          change tracePi A B ∈ universes.level (range.eval ρ)
          simpa only [Nat.max_self] using universes.products (range.eval ρ) (range.eval ρ) A B hb hb
            (universes.proposition_codes _ hb hA) hB
      | sprop =>
          change tracePi A B ∈ universes.level (range.eval ρ)
          simpa only [Nat.max_self] using universes.products (range.eval ρ) (range.eval ρ) A B hb hb
            (universes.proposition_codes _ hb hA) hB
      | type domain => exact universes.products (domain.eval ρ) (range.eval ρ) A B ha hb hA hB

theorem local_length {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {Γ : Context} {values : LocalValues.{u}} (h : InterpretsLocal ρ universes globals Γ values) :
    values.length = Γ.length := by
  induction h with
  | nil => rfl
  | assumption _ _ _ ih => exact congrArg Nat.succ ih
  | definition _ _ _ _ ih => exact congrArg Nat.succ ih

theorem sort_rule {count : ℕ} (ρ : LevelName → ℕ) (universes : UniverseSets.{u} count) (globals : GlobalValues.{u})
    (values : LocalValues.{u}) (s : SortExpr LevelName) (hbudget : s.super.UsesBelow ρ count) :
    HasValueAt ρ universes.level globals values (.sort s) (.sort s.super) :=
  ⟨sortValue ρ universes.level s, sortValue ρ universes.level s.super,
    Evaluates.sort, Evaluates.sort, sort_super ρ universes s hbudget⟩

/-- Preservation of every current CIC product-sort policy follows from local universe closure and concrete Prop closure. -/
theorem product_rule {count : ℕ} {ρ : LevelName → ℕ} (universes : UniverseSets.{u} count) {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {na : Binder} {domain codomain : Expr} {A : Value.{u}} {B : A → Value.{u}}
    {s1 s2 : SortExpr LevelName}
    (hs1 : s1.UsesBelow ρ count) (hs2 : s2.UsesBelow ρ count)
    (hA : Evaluates ρ universes.level globals values domain A) (hAsort : A ∈ sortValue ρ universes.level s1)
    (hB : ∀ x : A, Evaluates ρ universes.level globals ((x : Value.{u}) :: values) codomain (B x))
    (hBsort : ∀ x, B x ∈ sortValue ρ universes.level s2) :
    HasValueAt ρ universes.level globals values (.prod na domain codomain) (.sort (s1.product s2)) :=
  ⟨tracePi A B, sortValue ρ universes.level (s1.product s2), Evaluates.product hA hB,
    Evaluates.sort, sort_product ρ universes hs1 hs2 hAsort hBsort⟩

/-- The semantic premise for each lambda body is checked in the actual extended local environment. -/
theorem lambda_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {Γ : Context} {values : LocalValues.{u}} {na : Binder} {domain codomain body : Expr}
    {A : Value.{u}} {B : A → Value.{u}}
    (hΓ : InterpretsLocal ρ universes globals Γ values)
    (hA : Evaluates ρ universes globals values domain A)
    (hB : ∀ x : A, Evaluates ρ universes globals ((x : Value.{u}) :: values) codomain (B x))
    (hbody : ∀ x : A,
      InterpretsLocal ρ universes globals ({ binder := na, type := domain } :: Γ) ((x : Value.{u}) :: values) →
      ∃ v, Evaluates ρ universes globals ((x : Value.{u}) :: values) body v ∧ v ∈ B x) :
    HasValueAt ρ universes globals values (.lam na domain body) (.prod na domain codomain) := by
  classical
  have hvalues : ∀ x : A, ∃ v, Evaluates ρ universes globals ((x : Value.{u}) :: values) body v ∧ v ∈ B x :=
    fun x => hbody x (InterpretsLocal.assumption hΓ hA x.property)
  choose f heval hmember using hvalues
  exact ⟨traceLambda A f, tracePi A B, Evaluates.lambda hA heval,
    Evaluates.product hA hB, tracePi_intro f hmember⟩

/-- Actual CIC product syntax denotes an impredicative Prop, for every semantic domain set. -/
theorem product_prop_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {na : Binder} {domain codomain : Expr} {A : Value.{u}} {B : A → Value.{u}}
    (hA : Evaluates ρ universes globals values domain A)
    (hB : ∀ x : A, Evaluates ρ universes globals ((x : Value.{u}) :: values) codomain (B x))
    (hsorted : ∀ x : A, B x ∈ (propositionUniverse : Value.{u})) :
    HasValueAt ρ universes globals values (.prod na domain codomain) (.sort .prop) :=
  ⟨tracePi A B, propositionUniverse, Evaluates.product hA hB, Evaluates.sort, tracePi_propositionUniverse hsorted⟩

/-- SProp's truth-value denotation has the same product closure, without adding syntactic cumulativity. -/
theorem product_sprop_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {na : Binder} {domain codomain : Expr} {A : Value.{u}} {B : A → Value.{u}}
    (hA : Evaluates ρ universes globals values domain A)
    (hB : ∀ x : A, Evaluates ρ universes globals ((x : Value.{u}) :: values) codomain (B x))
    (hsorted : ∀ x : A, B x ∈ (propositionUniverse : Value.{u})) :
    HasValueAt ρ universes globals values (.prod na domain codomain) (.sort .sprop) :=
  ⟨tracePi A B, propositionUniverse, Evaluates.product hA hB, Evaluates.sort, tracePi_propositionUniverse hsorted⟩

/-- Application of actual CIC syntax inhabits the selected dependent semantic fibre. -/
theorem application_fibre {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {function argument : Expr} {A : Value.{u}} {B : A → Value.{u}}
    {f : Value.{u}} (x : A)
    (hf : Evaluates ρ universes globals values function f) (hmember : f ∈ tracePi A B)
    (hx : Evaluates ρ universes globals values argument x) :
    Evaluates ρ universes globals values (.app function argument) (traceApply f x) ∧ traceApply f x ∈ B x :=
  ⟨Evaluates.application hf hx, tracePi_elim hmember x⟩

/-- Identifying the syntactic substituted codomain requires a separate substitution-coherence proof. -/
theorem application_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {function argument codomain : Expr} {A : Value.{u}} {B : A → Value.{u}}
    {f : Value.{u}} (x : A)
    (hf : Evaluates ρ universes globals values function f) (hmember : f ∈ tracePi A B)
    (hx : Evaluates ρ universes globals values argument x)
    (hsubst : Evaluates ρ universes globals values (codomain.subst [argument] 0) (B x)) :
    HasValueAt ρ universes globals values (.app function argument) (codomain.subst [argument] 0) :=
  ⟨traceApply f x, B x, Evaluates.application hf hx, hsubst, tracePi_elim hmember x⟩

/-- Typed-domain beta is connected to an actual CIC lambda/application expression. -/
theorem evaluates_beta {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {na : Binder} {domain body argument : Expr} {A : Value.{u}} {f : A → Value.{u}}
    (hA : Evaluates ρ universes globals values domain A)
    (hf : ∀ x : A, Evaluates ρ universes globals ((x : Value.{u}) :: values) body (f x))
    (x : A) (hx : Evaluates ρ universes globals values argument x) :
    Evaluates ρ universes globals values (.app (.lam na domain body) argument) (f x) := by
  simpa only [trace_beta] using Evaluates.application (Evaluates.lambda (na := na) hA hf) hx

/-- A constant's actual assigned inhabitant, never a default set, proves its closed rule instance. -/
theorem constant_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {sig : GlobalContext} (hglobals : InterpretsConstants ρ universes globals sig)
    {name : String} {ui : List Universe} {declaration : ConstantBody}
    (hlookup : sig.environment.lookupConstant name = some declaration) (hinstance : sig.ValidInstance declaration.universes ui) :
    HasValueAt ρ universes globals [] (.constant name ui) (Expr.instantiate ui declaration.type) := by
  obtain ⟨A, value, hvalue, htype, hmember, hbody⟩ := hglobals.declarations name ui declaration hlookup hinstance
  exact ⟨value, A, Evaluates.constant hvalue, htype, hmember⟩

theorem identity_has_value (ρ : LevelName → ℕ) (universes : ℕ → Value.{u}) (globals : GlobalValues.{u}) :
    HasValueAt ρ universes globals [] propositionIdentity propositionIdentityType := by
  apply lambda_rule (A := propositionUniverse) (B := fun _ => propositionUniverse) InterpretsLocal.nil Evaluates.sort
  · exact fun _ => Evaluates.sort
  · intro x hcontext
    exact ⟨x, Evaluates.rel rfl, x.property⟩

theorem identity_applied_local (ρ : LevelName → ℕ) (universes : ℕ → Value.{u}) (globals : GlobalValues.{u})
    (P : Value.{u}) (hP : P ∈ (propositionUniverse : Value.{u})) :
    InterpretsLocal ρ universes globals [{ binder := {}, type := .sort .prop }] [P] ∧
    HasValueAt ρ universes globals [P] (.app propositionIdentity (.rel 0)) (.sort .prop) := by
  have hcontext : InterpretsLocal ρ universes globals [{ binder := {}, type := .sort .prop }] [P] :=
    InterpretsLocal.assumption InterpretsLocal.nil Evaluates.sort hP
  have happ : Evaluates ρ universes globals [P] (.app propositionIdentity (.rel 0)) P := by
    exact evaluates_beta (A := propositionUniverse) (f := fun x => (x : Value.{u}))
      (na := {}) (domain := .sort .prop) (body := .rel 0) Evaluates.sort
      (fun _ => Evaluates.rel rfl) ⟨P, hP⟩ (Evaluates.rel rfl)
  exact ⟨hcontext, P, propositionUniverse, happ, Evaluates.sort, hP⟩

theorem traceLambda_empty_domain (f : (∅ : Value.{u}) → Value.{u}) : traceLambda ∅ f = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [ZFSet.notMem_empty, iff_false]
  intro h
  obtain ⟨x, y, hy, heq⟩ := mem_traceLambda.mp h
  exact ZFSet.notMem_empty _ x.property

theorem traceApply_empty (x : Value.{u}) : traceApply ∅ x = ∅ := by
  apply ZFSet.ext
  intro y
  simp [mem_traceApply]

/-- Extending beta to a total function outside the trace's domain is false, even for an empty domain. -/
theorem off_domain_beta_counterexample :
    traceApply (traceLambda (∅ : Value.{u}) (fun _ => ({∅} : Value.{u}))) ∅ ≠ ({∅} : Value.{u}) := by
  rw [traceLambda_empty_domain, traceApply_empty]
  intro heq
  have hmember : (∅ : Value.{u}) ∈ ({∅} : Value.{u}) := by simp
  rw [← heq] at hmember
  exact ZFSet.notMem_empty _ hmember

end Silmaril.Proofs.Logic.TypeTheory.CIC.SetSemanticsLaws
