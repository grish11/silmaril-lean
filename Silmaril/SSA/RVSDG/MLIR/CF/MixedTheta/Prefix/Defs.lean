module

public import Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Prefix.Defs
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Defs

/-! # Splice a recovered mixed θ into one checked continuation leaf -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix

open Silmaril.MLIR
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Operands i1)
open LambdaSSA
open LambdaSSA.Acyclic.Theta
open LambdaSSA.Acyclic.Theta.Translation
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A : τ} {w : Width}

/-- A canonical loop leaf with a single ordinary instruction between its two
classifiers. Its entry, intermediate values, and exits share one word sort. -/
structure Leaf (Φ : Type) [HasTy Φ τ] (A : τ) where
  header : TwoBlock.Instruction Φ A (PureGamma.Choice A)
  body : TwoBlock.Instruction Φ A A
  join : TwoBlock.Instruction Φ A (PureGamma.Choice A)

def Leaf.loop (s : Leaf Φ A) : Loop Φ A A A A A :=
  ⟨s.header, .instruction s.body, s.join⟩

abbrev Rows (A : τ) := [Sequential.Flat.Serial.WirePorts A A A]
abbrev Graph (Φ ε : Type) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ) :=
  PureTheta.Prefix.Graph Φ ε A A A A A A (Rows A)

def Leaf.syntax (s : Leaf Φ A) : StructuredCFG.WithNestedFeedback.Syntax Φ A A A A A A (Rows A) :=
  .structured (.loop s.loop)

/-- Exact recovery of the whole input certifies the carrier handoff. The
suffix equality selects the one admitted canonical continuation shape. -/
structure Admission (g : Graph Φ ε A) where
  recovered : PureTheta.Prefix.Fibre g
  leaf : Leaf Φ A
  suffix : recovered.shape.tail = leaf.syntax.graph

private def readLoop [DecidableEq τ] {B K E D : τ} (s : Loop Φ A B K E D) : Option (Leaf Φ A) := by
  if h : (B, K, E, D) = (A, A, A, A) then
    obtain ⟨rfl, rfl, rfl, rfl⟩ := by simpa only [Prod.mk.injEq] using h
    obtain ⟨header, body, join⟩ := s
    cases body with
    | instruction op => exact some ⟨header, op, join⟩
    | _ => exact none
  else exact none

private def readLeaf [DecidableEq τ] {X Z L E D : τ}
    {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {tail : Sequential.Flat.Serial.Graph Φ A X Z L E D sigs}
    (f : Translation.Fibre .mixed tail) : Option (Leaf Φ A) := by
  obtain ⟨region, witness⟩ := f
  change StructuredCFG.WithNestedFeedback.Related A X Z L E D sigs region tail at witness
  cases witness with
  | generated code =>
    cases code with
    | structured code =>
      cases code with
      | loop s => exact readLoop s
      | _ => exact none
    | _ => exact none

/-- Recover the actual numbered table and read the single admitted leaf from
its canonical continuation witness. -/
@[no_expose] def recover [DecidableEq τ] [DecidableEq Φ] (g : Graph Φ ε A) : Option (Admission g) := do
  let head ← PureTheta.Prefix.recover g
  let leaf ← readLeaf head.shape.continuation
  letI := NestedTheta.Equality.decideGraph
    (Sequential.Flat.Numbered.Recognize.opcodeCode (τ := τ) (Φ := Φ)) head.shape.tail leaf.syntax.graph
  if suffix : head.shape.tail = leaf.syntax.graph then
    return ⟨head, leaf, suffix⟩
  else none

/-- The continuation emits its own calls and selects one arm of each
classifier. A branch-local value is in front of the input environment. -/
inductive Tail (Φ : Type) [HasTy Φ τ] (A : τ) (w : Width) : List Width → Type where
  | result {Γ : List Width} (again exit : Bool) (arg : Var Γ w) : Tail Φ A w Γ
  | call {Γ : List Width} (op : TwoBlock.Instruction Φ A A) (arg : Var Γ w)
      (rest : Tail Φ A w (w :: Γ)) : Tail Φ A w Γ
  | choose {Γ : List Width} (op : TwoBlock.Instruction Φ A (PureGamma.Choice A)) (arg : Var Γ w)
      (left right : Tail Φ A w (w :: Γ)) : Tail Φ A w Γ

def Leaf.code (s : Leaf Φ A) : Tail Φ A w [w,w] :=
  .choose s.header .here (.result false false .here)
    (.call s.body .here (.choose s.join .here (.result false true .here) (.result true false .here)))

inductive Body (Φ ε : Type) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ) (w : Width) :
    List Width → List Width → Type where
  | prefix {Γ Δ : List Width} : MixedTheta.Body Φ ε A w Γ Δ → Body Φ ε A w Γ Δ
  | suffix {Γ : List Width} : Tail Φ A w Γ → Body Φ ε A w Γ [i1,i1,w]

inductive Label (w : Width) : List Width → Type where
  | activate : Label w [w]
  | seam : Label w [w]
  | suffix : Label w [w]
  | exit : Label w [i1,w]

abbrev Cfg (Φ ε : Type) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ) (w : Width) :=
  CF.Ordered.Cfg (Body Φ ε A w) (Label w) [w] [i1,w]

/-- Replace the recovered prefix's return with a typed branch to the
continuation. The active carrier injection is represented by the suffix
entry label and its block argument. -/
def emit (head : PureTheta.Loop Φ ε A) (order : Bool) (leaf : Leaf Φ A) : Cfg Φ ε A w where
  entry := ⟨.prefix (.yield (.cons .here .nil)), .br ⟨.activate, .cons .here .nil⟩⟩
  block
    | .activate => ⟨.prefix (MixedTheta.activation head order),
        .condBr .here ⟨.activate, .cons (.there .here) .nil⟩ ⟨.seam, .cons (.there .here) .nil⟩⟩
    | .seam => ⟨.prefix (.yield (.cons .here .nil)), .br ⟨.suffix, .cons .here .nil⟩⟩
    | .suffix => ⟨.suffix leaf.code,
        .condBr .here ⟨.suffix, .cons (.there (.there .here)) .nil⟩
          ⟨.exit, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩⟩
    | .exit =>
      let values := Operands.cons .here (.cons (.there .here) .nil)
      ⟨.prefix (.yield values), .ret (.cons .here (.cons (.there .here) .nil))⟩

def lower (w : Width) {g : Graph Φ ε A} (f : Admission g) : Cfg Φ ε A w :=
  emit f.recovered.shape.loop f.recovered.shape.pureFirst f.leaf

section Semantics

variable [Isotope.Subtyping τ] [TypeModel.{0,0} τ]
variable {M : Type → Type} [Monad M]

def Tail.eval (codec : TyDen A ≃ BitVec w.val)
    (call : TwoBlock.Instruction Φ A A → TyDen A → M (TyDen A))
    (choose : TwoBlock.Instruction Φ A (PureGamma.Choice A) → TyDen A → M (TyDen A ⊕ TyDen A)) :
    {Γ : List Width} → Tail Φ A w Γ → Env Γ → M (Env [i1,i1,w])
  | _, .result again exit arg, env =>
    pure (.cons (BitVec.ofBool again) (.cons (BitVec.ofBool exit) (.cons (env.get arg) .nil)))
  | _, .call op arg rest, env => do
    let x ← call op (codec.symm (env.get arg))
    eval codec call choose rest (.cons (codec x) env)
  | _, .choose op arg left right, env => do
    match ← choose op (codec.symm (env.get arg)) with
    | .inl x => eval codec call choose left (.cons (codec x) env)
    | .inr x => eval codec call choose right (.cons (codec x) env)

variable {σ : Type} [InstructionModel Φ τ ε (StateT σ Part)] {Γ Δ : List Width}

def eval (codec : TyDen A ≃ BitVec w.val) : Body Φ ε A w Γ Δ → Env Γ → StateT σ Part (Env Δ)
  | .prefix code => MixedTheta.eval codec code
  | .suffix code => code.eval codec (TwoBlock.call (ε := ε)) (TwoBlock.TwoExit.callCase (ε := ε))

/-- The explicit i1 return tag preserves the two canonical exit labels. -/
def exitPacket (codec : TyDen A ≃ BitVec w.val) : LabelDen [A,A] → Env [i1,w]
  | .inl x => .cons (BitVec.ofBool false) (packet codec x)
  | .inr (.inl x) => .cons (BitVec.ofBool true) (packet codec x)
  | .inr (.inr impossible) => impossible.elim

end Semantics

end Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta.Prefix
