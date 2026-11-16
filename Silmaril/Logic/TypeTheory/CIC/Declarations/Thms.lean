module

public import Silmaril.Logic.TypeTheory.CIC.Declarations.Defs
public import Silmaril.Proofs.Logic.TypeTheory.CIC.Declarations

@[expose] public section

/-! # Checked CIC declarations and strict-positivity consequences -/

namespace Silmaril.Logic.TypeTheory.CIC

/-- Strict positivity excludes every mutual-block name from a function argument's domain. -/
theorem PositiveArgument.product_domain_closed {block : MutualInductiveBody} {depth : ℕ}
    {t : Expr} (h : PositiveArgument block depth t) :
    ∀ na A B, t = .prod na A B → A.isClosed depth = true :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.DeclarationLaws.positiveArgument_product_domain h

/-- The codomain of an actually positive product is itself positive under the binder. -/
theorem PositiveArgument.product_codomain_positive {block : MutualInductiveBody} {depth : ℕ}
    {t : Expr} (h : PositiveArgument block depth t) :
    ∀ na A B, t = .prod na A B → PositiveArgument block (depth + 1) B :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.DeclarationLaws.positiveArgument_product_codomain h

/-- The domain and codomain of an actual constructor product retain their source positivity derivations. -/
theorem PositiveConstructor.product_parts {block : MutualInductiveBody} {member depth : ℕ} {t : Expr}
    (h : PositiveConstructor block member depth t) :
    ∀ na A C, t = .prod na A C → PositiveArgument block depth A ∧ PositiveConstructor block member (depth + 1) C :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.DeclarationLaws.positiveConstructor_product_parts h

/-- A direct negative occurrence of the first mutual member cannot be a positive argument. -/
theorem PositiveArgument.negative_function (block : MutualInductiveBody) :
    ¬ PositiveArgument block 0 (.prod {} (.rel 0) (.sort .prop)) :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.DeclarationLaws.negativeFunctionArgument block

/-- Checked ordered declarations cannot shadow an earlier global name. -/
theorem CoreCheckedDeclarations.names_nodup {levels : List String}
    {constraints : List UniverseConstraint} {declarations : List (String × GlobalDeclaration)}
    (h : CoreCheckedDeclarations levels constraints declarations) :
    (declarations.map Prod.fst).Nodup :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.DeclarationLaws.declarations_names_nodup h

/-- Every declared constructor has a genuine derivation of the explicit positivity judgment. -/
theorem CoreCheckedBlock.constructor_positive {sig : GlobalContext} {name : String}
    {block : MutualInductiveBody} {member index : ℕ} {body : InductiveBody}
    {constructor : ConstructorBody} (h : CoreCheckedBlock sig name block)
    (hb : block.bodies[member]? = some body)
    (hc : body.constructors[index]? = some constructor) :
    PositiveConstructor block member 0 constructor.type :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.DeclarationLaws.checked_constructor_positive h hb hc

/-- The declaration checks admit the actual empty-parameter natural-number block and both constructors. -/
theorem DeclarationExamples.naturalEnvironment_checked :
    CoreCheckedEnvironment DeclarationExamples.naturalEnvironment :=
  Silmaril.Proofs.Logic.TypeTheory.CIC.DeclarationLaws.Natural.environment_checked

end Silmaril.Logic.TypeTheory.CIC
