module

public import Silmaril.SSA.MLIR.CF.Ordered.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta.Reverse.Defs

/-! # Recovered mixed θ in the project-defined ordered CF contract -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta

open Silmaril.MLIR
open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.Pure (Operands i1)
open LambdaSSA.Acyclic.Theta.Translation
open Isotope.LetIter.ProofRelevant.Semantics (TypeModel TyDen InstructionModel)

variable {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A : τ} {w : Width}

/-- The admitted body has a bottom-effect value binding and a separate
ordered binding whose observed result is the restart bit. -/
inductive Body (Φ ε : Type) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ) (w : Width) :
    List Width → List Width → Type where
  | yield {Γ Δ : List Width} (args : Operands Γ Δ) : Body Φ ε A w Γ Δ
  | value {Γ Δ : List Width} (op : LambdaSSA.TwoBlock.Instruction Φ A A) (bottom : (instrEff op.op : ε) = ⊥)
      (arg : Var Γ w) (rest : Body Φ ε A w (w :: Γ) Δ) : Body Φ ε A w Γ Δ
  | classify {Γ Δ : List Width} (op : LambdaSSA.TwoBlock.Instruction Φ A (PureGamma.Choice A))
      (arg : Var Γ w) (rest : Body Φ ε A w (i1 :: Γ) Δ) : Body Φ ε A w Γ Δ

inductive Label (w : Width) : List Width → Type where
  | activate : Label w [w]
  | exit : Label w [w]

abbrev Cfg (Φ ε : Type) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ) (w : Width) :=
  CF.Ordered.Cfg (Body Φ ε A w) (Label w) [w] [w]

def activation (s : PureTheta.Loop Φ ε A) (pureFirst : Bool) : Body Φ ε A w [w,w] [i1,w] :=
  if pureFirst then
    .value s.value s.bottom .here (.classify s.decide (.there .here) (.yield (.cons .here (.cons (.there .here) .nil))))
  else
    .classify s.decide .here (.value s.value s.bottom (.there .here) (.yield (.cons (.there .here) (.cons .here .nil))))

def emit (s : PureTheta.Loop Φ ε A) (pureFirst : Bool) : Cfg Φ ε A w where
  entry := ⟨.yield (.cons .here .nil), .br ⟨.activate, .cons .here .nil⟩⟩
  block
    | .activate => ⟨activation s pureFirst,
        .condBr .here ⟨.activate, .cons (.there .here) .nil⟩ ⟨.exit, .cons (.there .here) .nil⟩⟩
    | .exit => ⟨.yield (.cons .here .nil), .ret (.cons .here .nil)⟩

/-- The fibre certifies the actual graph, including row order and the source
of the token at both the backedge and the exit. -/
def lower (w : Width) {g : PureTheta.Reverse.Graph Φ ε A} (f : PureTheta.Reverse.Fibre g) :
    Cfg Φ ε A w :=
  emit f.loop f.pureFirst

section Semantics

variable [Isotope.Subtyping τ] [TypeModel.{0,0} τ]
variable {M : Type → Type} [Monad M]

/-- Carry conversion must be exact at the chosen width. The ordered
classifier runs in the block monad, which supplies its live store. -/
def Body.eval (codec : TyDen A ≃ BitVec w.val)
    (value : (op : LambdaSSA.TwoBlock.Instruction Φ A A) →
      (instrEff op.op : ε) = ⊥ → TyDen A → TyDen A)
    (classify : LambdaSSA.TwoBlock.Instruction Φ A (PureGamma.Choice A) → TyDen A → M Bool) :
    {Γ Δ : List Width} → Body Φ ε A w Γ Δ → Env Γ → M (Env Δ)
  | _, _, .yield args, env => pure (args.eval env)
  | _, _, .value op bottom arg rest, env =>
    eval codec value classify rest (.cons (codec (value op bottom (codec.symm (env.get arg)))) env)
  | _, _, .classify op arg rest, env => do
    let again ← classify op (codec.symm (env.get arg))
    eval codec value classify rest (.cons (BitVec.ofBool again) env)

variable {σ : Type} {Γ Δ : List Width} [InstructionModel Φ τ ε (StateT σ Part)]

/-- Interpret the source classifier with its ordered, partial semantics.
Either successful branch inherits exactly the returned store. -/
def eval (codec : TyDen A ≃ BitVec w.val) (body : Body Φ ε A w Γ Δ) (env : Env Γ) :
    StateT σ Part (Env Δ) :=
  body.eval codec (fun op bottom => LambdaSSA.PureRow.pureCall (σ := σ) op bottom)
    (fun op x => LambdaSSA.TwoBlock.TwoExit.callCase (ε := ε) op x >>= fun route =>
      pure (route.elim (fun _ => false) (fun _ => true))) env

def packet (codec : TyDen A ≃ BitVec w.val) (x : TyDen A) : Env [w] := .cons (codec x) .nil

/-- The result of one activation before its typed conditional terminator. -/
def activationPacket (codec : TyDen A ≃ BitVec w.val) (route : TyDen A ⊕ TyDen A) : Env [i1,w] :=
  match route with
  | .inl x => .cons (BitVec.ofBool false) (packet codec x)
  | .inr x => .cons (BitVec.ofBool true) (packet codec x)

end Semantics

end Silmaril.SSA.RVSDG.MLIR.CF.MixedTheta
