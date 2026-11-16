module

public import Silmaril.Logic.TypeTheory.CIC.Declarations.Defs
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.DeclarationLaws

open Silmaril.Logic.TypeTheory.CIC

private theorem head_mkApps (t : Expr) (args : List Expr) :
    Expr.head (Expr.mkApps t args) = Expr.head t := by
  induction args generalizing t with
  | nil => rfl
  | cons a args ih => simpa only [Expr.mkApps, List.foldl_cons, Expr.head] using ih (.app t a)

theorem positiveArgument_product_domain {block : MutualInductiveBody} {depth : ℕ} {t : Expr}
    (h : PositiveArgument block depth t) :
    ∀ na A B, t = .prod na A B → A.isClosed depth = true := by
  induction h with
  | @closed depth t hc =>
      intro na A B ht
      cases ht
      have hprod : (A.isClosed depth && B.isClosed (depth + 1)) = true := by
        simpa only [Term.isClosed] using hc
      exact (Bool.and_eq_true_iff.mp hprod).1
  | recursive hlookup hlength hargs =>
      intro na A B ht
      have hh := congrArg Expr.head ht
      simp only [head_mkApps, Expr.head] at hh
      contradiction
  | letIn _ _ => intro na A B ht; cases ht
  | product hA _ _ => intro na A B ht; cases ht; exact hA

/-- Product positivity supplies codomain positivity, including the wholly closed source case. -/
theorem positiveArgument_product_codomain {block : MutualInductiveBody} {depth : ℕ} {t : Expr}
    (h : PositiveArgument block depth t) :
    ∀ na A B, t = .prod na A B → PositiveArgument block (depth + 1) B := by
  induction h with
  | @closed depth t hc =>
      intro na A B ht
      cases ht
      have hprod : (A.isClosed depth && B.isClosed (depth + 1)) = true := by simpa only [Term.isClosed] using hc
      exact .closed (Bool.and_eq_true_iff.mp hprod).2
  | recursive _ _ _ =>
      intro na A B ht
      have hh := congrArg Expr.head ht
      simp only [head_mkApps, Expr.head] at hh
      contradiction
  | letIn _ _ => intro na A B ht; cases ht
  | product _ hB _ => intro na A B ht; cases ht; exact hB

/-- A raw constructor product retains both actual source positivity derivations. -/
theorem positiveConstructor_product_parts {block : MutualInductiveBody} {member depth : ℕ} {t : Expr}
    (h : PositiveConstructor block member depth t) :
    ∀ na A C, t = .prod na A C → PositiveArgument block depth A ∧ PositiveConstructor block member (depth + 1) C := by
  induction h with
  | conclusion _ _ =>
      intro na A C ht
      have hh := congrArg Expr.head ht
      simp only [head_mkApps, Expr.head] at hh
      contradiction
  | letIn _ _ => intro na A C ht; cases ht
  | product hA hC _ => intro na A C ht; cases ht; exact ⟨hA, hC⟩

theorem negativeFunctionArgument (block : MutualInductiveBody) :
    ¬ PositiveArgument block 0 (.prod {} (.rel 0) (.sort .prop)) := by
  intro h
  have hc : (Term.rel 0 : Expr).isClosed 0 = true := positiveArgument_product_domain h _ _ _ rfl
  simp [Term.isClosed] at hc

theorem declarations_names_nodup {levels : List String} {constraints : List UniverseConstraint}
    {declarations : List (String × GlobalDeclaration)}
    (h : CoreCheckedDeclarations levels constraints declarations) :
    (declarations.map Prod.fst).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | cons _ hfresh _ ih => exact List.nodup_cons.mpr ⟨hfresh, ih⟩

theorem checked_constructor_positive {sig : GlobalContext} {name : String}
    {block : MutualInductiveBody} {member index : ℕ} {body : InductiveBody}
    {constructor : ConstructorBody} (h : CoreCheckedBlock sig name block)
    (hb : block.bodies[member]? = some body)
    (hc : body.constructors[index]? = some constructor) :
    PositiveConstructor block member 0 constructor.type := by
  obtain ⟨sorts, hlength, hctors, _⟩ := (h.members member body hb).constructors
  obtain ⟨hindex, _⟩ := List.getElem?_eq_some_iff.mp hc
  have hsort : index < sorts.length := by omega
  exact (hctors index constructor sorts[index] hc (List.getElem?_eq_getElem hsort)).positive

namespace Natural

open DeclarationExamples

private def sig : GlobalContext := { environment := {} }

private theorem wf_arities : CoreWfLocal sig naturalBlock.aritiesContext := by
  apply CoreWfLocal.assumption .nil (s := .type (.succ .zero))
  · exact CoreTyping.sort .nil trivial
  · rfl

private theorem type_N :
    CoreTyping sig naturalBlock.aritiesContext (.rel 0) (.sort (.type .zero)) := by
  simpa only [naturalBody, Term.lift] using CoreTyping.rel (n := 0) wf_arities rfl

private theorem wf_argument : CoreWfLocal sig
    ({ binder := {}, type := .rel 0 } :: naturalBlock.aritiesContext) :=
  CoreWfLocal.assumption wf_arities type_N rfl

private theorem type_N_under_argument : CoreTyping sig
    ({ binder := {}, type := .rel 0 } :: naturalBlock.aritiesContext)
    (.rel 1) (.sort (.type .zero)) := by
  simpa only [naturalBody, Term.lift] using CoreTyping.rel (n := 1) wf_argument rfl

private theorem zero_checked :
    CoreCheckedConstructor sig naturalBlock 0 naturalBody naturalZero [] where
  arity := rfl
  shape := rfl
  type_sorted := ⟨.type .zero, type_N, rfl⟩
  argument_sorts := .nil
  indices := .nil
  positive := PositiveConstructor.conclusion (block := naturalBlock) (member := 0)
    (depth := 0) (args := []) (by decide) (by simp)

private theorem successor_argument_positive : PositiveArgument naturalBlock 0 (.rel 0) := by
  apply PositiveArgument.recursive (index := 0) (body := naturalBody) (args := [])
  · exact ⟨Nat.zero_le 0, by decide, rfl⟩
  · rfl
  · simp

private theorem successor_checked :
    CoreCheckedConstructor sig naturalBlock 0 naturalBody naturalSuccessor [.type .zero] where
  arity := rfl
  shape := rfl
  type_sorted := ⟨.type (.max .zero .zero), CoreTyping.product (na := {}) type_N rfl type_N_under_argument, rfl⟩
  argument_sorts := CoreContextSorts.assumption .nil type_N rfl
  indices := .nil
  positive := PositiveConstructor.product successor_argument_positive
    (PositiveConstructor.conclusion (block := naturalBlock) (member := 0)
      (depth := 1) (args := []) (by decide) (by simp))

private theorem constructors_checked (index : ℕ) (constructor : ConstructorBody)
    (sorts : List (SortExpr LevelName))
    (hc : naturalBody.constructors[index]? = some constructor)
    (hs : [[], [.type .zero]][index]? = some sorts) :
    CoreCheckedConstructor sig naturalBlock 0 naturalBody constructor sorts := by
  cases index with
  | zero => cases Option.some.inj hc; cases Option.some.inj hs; exact zero_checked
  | succ index =>
      cases index with
      | zero => cases Option.some.inj hc; cases Option.some.inj hs; exact successor_checked
      | succ index => simp [naturalBody] at hc

private theorem body_checked : CoreCheckedInductive sig "nat" naturalBlock 0 naturalBody where
  shape := rfl
  arity_sorted := ⟨.type (.succ .zero), CoreTyping.sort .nil trivial, rfl⟩
  constructors := ⟨[[], [.type .zero]], rfl, constructors_checked, by
    simp [InductiveBody.ValidSorts, naturalBody, SortExpr.Cumul, UniverseExpr.eval]⟩
  projections := Or.inl rfl
  relevance := rfl

private theorem block_checked : CoreCheckedBlock sig "nat" naturalBlock where
  members := by
    intro member body hb
    cases member with
    | zero => cases Option.some.inj hb; exact body_checked
    | succ member => simp [naturalBlock] at hb
  parameters := .nil
  parameter_count := rfl
  no_variance := rfl

private theorem universes_checked : naturalBlock.universes.WellFormed {} :=
  ⟨by simp [GlobalContext.forDeclaration, naturalBlock],
   ⟨fun _ => 0, by simp [GlobalContext.Satisfies, GlobalContext.forDeclaration, naturalBlock]⟩,
   by simp [naturalBlock]⟩

theorem environment_checked : CoreCheckedEnvironment naturalEnvironment := by
  refine ⟨List.nodup_nil, ?_, ?_, ?_⟩
  · simp [naturalEnvironment]
  · exact ⟨fun _ => 0, by simp [GlobalContext.Satisfies, naturalEnvironment]⟩
  · apply CoreCheckedDeclarations.cons .nil (by simp)
    exact ⟨universes_checked, block_checked⟩

end Natural

end Silmaril.Proofs.Logic.TypeTheory.CIC.DeclarationLaws
