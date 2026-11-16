module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Lowering.Defs
public import Silmaril.Logic.Kore.Operational.Conditional.Defs

/-! Builtin laws are a real restriction of native matching models. They do not
follow from ordinary declarations or from arbitrary constant interpretations. -/
-- Configurable builtin names intentionally have a canonical fallback instance.
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
variable [sorts : SortBindings]
open CategoryTheory Silmaril.Logic.Institution
variable {scope : Kore.Modules.Scope}

structure Carriers (M : Matching.GeneralFixedPoint.Model scope.signature) where
  integer : M.carrier sorts.intSort ≃ Int
  boolean : M.carrier sorts.boolSort ≃ Bool

def Carriers.literal {M : Matching.GeneralFixedPoint.Model scope.signature} (B : Carriers M) : (l : Literal) → M.carrier l.sort
  | .integer n => B.integer.symm n
  | .boolean b => B.boolean.symm b

/-- Every actual argument tuple is constrained, not just literal source calls.
Only the finitely declared literal operations inhabit the scope signature. -/
structure Laws (M : Matching.GeneralFixedPoint.Model scope.signature) (literalPrefix : String)
    (literals : List LiteralBinding) (hooks : List HookBinding) (B : Carriers M) : Prop where
  literal : ∀ b ∈ literals, ∀ (l : Literal), b.literal = l →
    ∀ (op : scope.signature.operations 0 (fun i => i.elim0) l.sort),
    op.val = b.symbol →
    M.operation op (fun i => i.elim0) = {B.literal l}
  intEq : ∀ b ∈ hooks, b.hook = .intEq →
    ∀ (op : scope.signature.operations 2 (fun _ => sorts.intSort) sorts.boolSort),
    op.val = b.symbol → ∀ args,
    M.operation op args = {B.boolean.symm (Operational.Conditional.intEqual
      (B.integer (args 0)) (B.integer (args 1)))}
  boolNot : ∀ b ∈ hooks, b.hook = .boolNot →
    ∀ (op : scope.signature.operations 1 (fun _ => sorts.boolSort) sorts.boolSort),
    op.val = b.symbol → ∀ args,
    M.operation op args = {B.boolean.symm (!(B.boolean (args 0)))}

structure Model (scope : Kore.Modules.Scope) (literalPrefix : String) (literals : List LiteralBinding) (hooks : List HookBinding) where
  native : Matching.GeneralFixedPoint.Model scope.signature
  carriers : Carriers native
  laws : Laws native literalPrefix literals hooks carriers

/-- Retain every actual native relational homomorphism between restricted
models. No claim that such arrows preserve complement satisfaction is made. -/
instance (literalPrefix : String) (literals : List LiteralBinding) (hooks : List HookBinding) : Category (Model scope literalPrefix literals hooks) where
  Hom M N := M.native ⟶ N.native
  id M := 𝟙 M.native
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

/-- A fixed-scope room of arbitrary native sentences on builtin models.
Transport to other signatures is a separate obligation, not silently inferred. -/
def nativeRoom (scope : Kore.Modules.Scope) (literalPrefix : String) (literals : List LiteralBinding) (hooks : List HookBinding) : Room :=
  ⟨Matching.GeneralFixedPoint.Sentence scope.signature, Cat.of (Model scope literalPrefix literals hooks),
    fun M p => Matching.GeneralFixedPoint.Sentence.Satisfies M.native p⟩

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
