module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.Executable.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.PureRow.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Renaming.Defs

/-! # A pure entry value for the public structured emitter -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix

open Isotope.LambdaSSA (Region Ren At)
open Isotope.LetIter.ProofRelevant.Semantics
open Sequential
open Sequential.Flat.Serial (payloadData)
open OrderedTheta (carried carriedData point)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open TwoBlock.TwoExit (Carrier enter)
open LinearChain.Wiring (newest)
open NestedTheta.ExplicitRuntime.Splice (weaken)


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A R B X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- The ordered entry action and total pure value both read the original
input. The action supplies the token and the pure value enters the body. -/
structure Prefix (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A R B : τ) where
  action : TwoBlock.Instruction Φ A R
  value : TwoBlock.Instruction Φ A B
  bottom : (instrEff value.op : ε) = ⊥

omit [TypeFormers τ] in
theorem keepEntry : Ren [B] [B,R,A] id := by
  intro i S h
  cases i with
  | zero => exact h
  | succ n => simp [At] at h

def region (setup : Prefix Φ ε A R B) (body : Source Φ B X Z L E D sigs) : Region Φ :=
  .let₁ (.op setup.action.op (.var 0)) <|
    .let₁ (.op setup.value.op (.var 1)) (body.fragment.region.renameVars id)

theorem typing (setup : Prefix Φ ε A R B) (body : Source Φ B X Z L E D sigs) :
    Region.HasType [A] (region setup body) [E,D] :=
  .let₁ (PureRow.typingAt setup.action rfl) (.let₁ (PureRow.typingAt setup.value rfl)
    (body.fragment.typing.renameVars keepEntry))

/-- A data-only opcode supplies the same typed input carrier as the ordered
compiler. Its bottom-effect proof is part of the label. -/
inductive EntryOp (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (B X Z : τ) :
    Dialect.{u,u} τ PUnit where
  | value {A : τ} (p : TwoBlock.Instruction Φ A B) (h : (instrEff p.op : ε) = ⊥) :
      EntryOp Φ ε B X Z (carried A) (carried (Carrier B X Z))

abbrev Op (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (B X Z : τ) :=
  NestedTheta.ExplicitRuntime.PurePrefix.Op (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (EntryOp Φ ε B X Z)

def Rows (R B X Z : τ) : Bool → List (Ports (OrderedRuntime.Structured.Ty τ))
  | false => [Threaded (carried R), carried (Carrier B X Z)]
  | true => [carried (Carrier B X Z), Threaded (carried R)]

abbrev orderedCall (p : TwoBlock.Instruction Φ A R) :
    OrderedRuntime.Structured.Instruction (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (carried A) (carried R) :=
  .effect (.loop (.acyclic (.call .direct p)))

def code (setup : Prefix Φ ε A R B) (body : Source Φ B X Z L E D sigs) (pureFirst : Bool) :
    NestedTheta.ExplicitRuntime.PurePrefix.Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (EntryOp Φ ε B X Z)
      (carriedData A) (payloadData L E D) (.arg (runtimePort (carried A))) (Rows R B X Z pureFirst ++ sigs) :=
  let entry : Origin (Threaded (carried A)) [] OrderedRuntime.Structured.runtime := .arg (runtimePort (carried A))
  let action := orderedCall setup.action
  let value := EntryOp.value (X := X) (Z := Z) setup.value setup.bottom
  match pureFirst with
  | false =>
    let previous := [Threaded (carried R)]
    let live := nextRuntime (args := Threaded (carried A)) [] (carried R)
    let next := NestedTheta.ExplicitRuntime.PurePrefix.attach (a := carriedData A) body.compileChecked
      (weaken (carried (Carrier B X Z)) live) (.cons (newest .head previous) .nil)
    ⟨_, .primitive entry (carriedData A) (carriedData R) action (.cons (.arg .head) .nil)
      (.pure live (carriedData A) (carriedData _) value (.cons (.arg .head) .nil) next.2)⟩
  | true =>
    let previous := [carried (Carrier B X Z)]
    let next := NestedTheta.ExplicitRuntime.PurePrefix.attach (a := carriedData A) body.compileChecked
      (nextRuntime previous (carried R)) (.cons (.output (0 : Fin 2) .head) .nil)
    ⟨_, .pure entry (carriedData A) (carriedData _) value (.cons (.arg .head) .nil)
      (.primitive (weaken (carried (Carrier B X Z)) entry) (carriedData A) (carriedData R) action
        (.cons (.arg .head) .nil) next.2)⟩

def compile (setup : Prefix Φ ε A R B) (body : Source Φ B X Z L E D sigs) (pureFirst : Bool := false) :=
  (code setup body pureFirst).1.toGraph

def compileChecked (setup : Prefix Φ ε A R B) (body : Source Φ B X Z L E D sigs) (pureFirst : Bool) :
    NestedTheta.ExplicitRuntime.PurePrefix.EntryChecked (a := carriedData A) (b := payloadData L E D)
      (compile setup body pureFirst).toTerm :=
  (NestedTheta.Term.toTerm_toGraph _).symm ▸ (code setup body pureFirst).2

def entryCode : NestedTheta.Equality.OpcodeCode (EntryOp Φ ε B X Z) where
  Key := Φ
  encode | .value p _ => p.op
  injective := by
    intro _ _ x y same
    cases x with
    | value p _ =>
      cases y with
      | value q _ =>
        have eq : p = q := by
          cases p
          cases q
          cases same
          rfl
        cases eq
        rfl

section Model

variable {σ : Type u} [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

def evalEntry :
    NestedTheta.ExplicitRuntime.PurePrefix.Total (Wires.wireModel (Φ := Φ) (ε := ε) (σ := σ)) (EntryOp Φ ε B X Z)
  | _, _, .value p h, .cons x .nil => .cons (enter (PureRow.pureCall (σ := σ) p h x)) .nil

abbrev model :=
  NestedTheta.ExplicitRuntime.PurePrefix.model (Wires.wireModel (Φ := Φ) (ε := ε) (σ := σ))
    (evalEntry (B := B) (X := X) (Z := Z))

def actions (base : Translation.Actions (τ := τ) (ε := ε) (σ := σ) Φ) :
    NestedTheta.Partial.Executable.Actions (model (Φ := Φ) (ε := ε) (σ := σ) (B := B) (X := X) (Z := Z)) :=
  NestedTheta.ExplicitRuntime.PurePrefix.actions _ _ base

end Model

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix
