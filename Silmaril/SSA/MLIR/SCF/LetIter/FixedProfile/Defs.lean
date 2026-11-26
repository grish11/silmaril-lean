module

public import Silmaril.SSA.MLIR.SCF.LetIter.ScalarWhile.Thms

/-! # Fixed-profile scalar programs and typed opcode renaming -/

@[expose] public section

namespace Silmaril.MLIR.SCF.LetIter.FixedProfile

open CategoryTheory
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.Pure (Code Eval OpSignature Operands)
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)

/-- The signature category changes opcodes while preserving their operand and result profiles. -/
structure Signature where
  op : OpSignature

/-- A family of renamings indexed by the ordered operand and result types. -/
structure Signature.Renaming (S T : Signature) where
  opcode {args : List Width} {w : Width} : S.op args w → T.op args w

instance : Category.{0} Signature where
  Hom := Signature.Renaming
  id _ := ⟨fun op => op⟩
  comp f g := ⟨fun op => g.opcode (f.opcode op)⟩

variable {S T U : Signature}

/-- Interpret source opcodes by their renamed target opcodes. -/
def reduct (f : S ⟶ T) (M : Eval T.op) : Eval S.op :=
  fun op => M (Signature.Renaming.opcode f op)

@[simp] theorem reduct_id (M : Eval S.op) : @reduct S S (𝟙 S) M = @M := rfl

theorem reduct_comp (f : S ⟶ T) (g : T ⟶ U) (M : Eval U.op) :
    @reduct S U (f ≫ g) M = @reduct S T f (@reduct T U g M) := rfl

/-- The four ordered scalar interfaces are fixed throughout the comparison. -/
structure Profile where
  input : List Width
  state : List Width
  payload : List Width
  result : List Width

variable (P : Profile)

abbrev Init := Operands P.input P.state
abbrev Before (S : Signature) := Code S.op (Condition P.payload) (P.state ++ P.input)
abbrev After (S : Signature) := Code S.op (Yield P.state) (P.payload ++ P.input)
abbrev Parent (S : Signature) := Code S.op (Return P.result) (P.payload ++ P.input)
abbrev Call (S : Signature) := ScalarWhile.Call S.op P.input P.result P.state P.payload

/-- A scalar while whose profile is fixed at the institution boundary. -/
structure Scalar (S : Signature) where
  init : Init P
  before : Before P S
  afterRegion : After P S
  parent : Parent P S

/-- Execute a fixed-profile program with the independently defined scalar while. -/
abbrev Scalar.toWhile (p : Scalar P S) : While S.op P.input P.result where
  State := P.state
  Payload := P.payload
  init := p.init
  before := p.before
  after := p.afterRegion
  cont := p.parent

variable {P}

/-- Rename only the operations in typed straight-line blocks. -/
def renameCode (f : S ⟶ T) {Term : List Width → Type} :
    {Γ : List Width} → Code S.op Term Γ → Code T.op Term Γ
  | _, .terminator term => .terminator term
  | _, .letOp op operands rest => .letOp (Signature.Renaming.opcode f op) operands (renameCode f rest)

@[simp] theorem renameCode_id {Term : List Width → Type} {Γ : List Width}
    (code : Code S.op Term Γ) : renameCode (𝟙 S) code = code := by
  induction code <;> simp_all [renameCode]
  rfl

theorem renameCode_comp (f : S ⟶ T) (g : T ⟶ U) {Term : List Width → Type} {Γ : List Width}
    (code : Code S.op Term Γ) : renameCode g (renameCode f code) = renameCode (f ≫ g) code := by
  induction code <;> simp_all [renameCode]
  rfl

theorem renameCode_eval (f : S ⟶ T) (M : Eval T.op) {Term : List Width → Type}
    {A : Type} (finish : ∀ {Γ}, Term Γ → Env Γ → A) {Γ : List Width}
    (code : Code S.op Term Γ) (env : Env Γ) :
    (renameCode f code).eval M finish env = code.eval (reduct f M) finish env := by
  induction code with
  | terminator => rfl
  | letOp _ _ _ ih => exact ih _

/-- The same opcode map acts on the four native primitive call forms. -/
def renameCall (f : S ⟶ T) : Call P S → Call P T
  | .init operands => .init operands
  | .before code => .before (renameCode f code)
  | .yield code => .yield (renameCode f code)
  | .parent code => .parent (renameCode f code)

theorem renameCall_id : renameCall (P := P) (𝟙 S) = id := by
  funext call
  cases call <;> simp [renameCall]

theorem renameCall_comp (f : S ⟶ T) (g : T ⟶ U) :
    renameCall (P := P) (f ≫ g) = renameCall g ∘ renameCall f := by
  funext call
  cases call <;> simp [renameCall, renameCode_comp]

/-- Signature reindexing for the typed scalar program. -/
def Scalar.rename (f : S ⟶ T) (p : Scalar P S) : Scalar P T where
  init := p.init
  before := renameCode f p.before
  afterRegion := renameCode f p.afterRegion
  parent := renameCode f p.parent

@[simp] theorem Scalar.rename_id (p : Scalar P S) : p.rename (𝟙 S) = p := by
  cases p
  simp [rename]

theorem Scalar.rename_comp (f : S ⟶ T) (g : T ⟶ U) (p : Scalar P S) :
    (p.rename f).rename g = p.rename (f ≫ g) := by
  cases p
  simp [rename, renameCode_comp]

theorem Scalar.runFrom_rename (f : S ⟶ T) (M : Eval T.op) (p : Scalar P S)
    (input : Env P.input) (fuel : Nat) (state : Env P.state) :
    (p.rename f).toWhile.runFrom M input fuel state =
      p.toWhile.runFrom (reduct f M) input fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [While.runFrom, toWhile, rename, renameCode_eval]
      split
      · exact ih _
      · rfl

theorem Scalar.run_rename (f : S ⟶ T) (M : Eval T.op) (p : Scalar P S)
    (input : Env P.input) (fuel : Nat) :
    (p.rename f).toWhile.run M fuel input = p.toWhile.run (reduct f M) fuel input :=
  p.runFrom_rename f M input fuel _

end Silmaril.MLIR.SCF.LetIter.FixedProfile
