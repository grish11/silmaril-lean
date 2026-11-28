module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma.Defs

/-! # A checked θ body with independent pure and ordered bindings -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta

open Isotope.LambdaSSA (Region)
open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (carried carriedData results resultData point exitValue)
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open LinearChain.Wiring (newest)
open NestedTheta.ExplicitRuntime.Splice (weaken)
open NestedTheta.ExplicitRuntime.PurePrefix (Code EntryChecked)
open Sequential
open PureGamma (Choice ValueOp Op)
open TwoBlock.TwoExit (callCase)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A : τ}

/-- Both instructions read the current carried value. The ordered instruction
selects exit or feedback, and the total pure instruction computes the payload
for either edge. -/
structure Loop (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A : τ) where
  value : TwoBlock.Instruction Φ A A
  bottom : (instrEff value.op : ε) = ⊥
  decide : TwoBlock.Instruction Φ A (Choice A)

def Loop.block (s : Loop Φ ε A) : Region Φ :=
  .let₁ (.op s.value.op (.var 0)) <|
    .case (.op s.decide.op (.var 1)) (.br 1 (.var 1)) (.br 0 (.var 1))

theorem Loop.blockTyping (s : Loop Φ ε A) : Region.HasType [A,A] s.block [A,A] :=
  .let₁ (PureRow.typingAt s.value rfl)
    (.case (PureRow.typingAt s.decide rfl) (.br rfl (.var rfl)) (.br rfl (.var rfl)))

def Loop.region (s : Loop Φ ε A) : Region Φ := .cfg (.br 0 (.var 0)) 1 (fun _ => s.block)

theorem Loop.typing (s : Loop Φ ε A) : Region.HasType [A] s.region [A] :=
  .cfg (fun _ => A) (.br rfl (.var rfl)) (fun _ => s.blockTyping)

abbrev decision (op : TwoBlock.Instruction Φ A (Choice A)) :
    OrderedRuntime.Structured.Instruction (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ)
      (carried A) (results (Choice A)) :=
  .effect (.loop (.acyclic (.classify .direct op)))

def bodyRows (A : τ) : Bool → List (Ports (OrderedRuntime.Structured.Ty τ))
  | true => [carried A, Threaded (results (Choice A))]
  | false => [Threaded (results (Choice A)), carried A]

/-- The result tag comes from the ordered instruction, the result value comes
from the pure instruction, and the returned token comes from the ordered
instruction in both placements. -/
def Loop.body (s : Loop Φ ε A) (pureFirst : Bool) :
    Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)
      (carriedData A) (resultData A) (.arg (runtimePort (carried A))) (bodyRows A pureFirst) :=
  let live := Origin.arg (past := []) (runtimePort (carried A))
  let arg {past : List (Ports (OrderedRuntime.Structured.Ty τ))} : Wires (Threaded (carried A)) past (carried A) :=
    .cons (.arg .head) .nil
  let value := ValueOp.call s.value s.bottom
  match pureFirst with
  | true =>
    let previous := [carried A]
    ⟨_, .pure live (carriedData A) (carriedData A) value arg <|
      .primitive (weaken (carried A) live) (carriedData A) (resultData _) (decision s.decide) arg <|
      .ret (nextRuntime previous (results (Choice A)))
        (.cons (newest .head previous) (.cons (.output (0 : Fin 2) .head) .nil))⟩
  | false =>
    let previous := [Threaded (results (Choice A))]
    let next := nextRuntime [] (results (Choice A))
    ⟨_, .primitive live (carriedData A) (resultData _) (decision s.decide) arg <|
      .pure next (carriedData A) (carriedData A) value arg <|
      .ret (weaken (carried A) next)
        (.cons (.output (0 : Fin 2) .head) (.cons (newest .head previous) .nil))⟩

def Loop.code (s : Loop Φ ε A) (pureFirst : Bool) :
    Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)
      (carriedData A) (carriedData A) (.arg (runtimePort (carried A))) [Threaded (carried A)] :=
  let body := s.body pureFirst
  ⟨_, .theta (.arg (runtimePort (carried A))) (carriedData A) (.cons (.arg .head) .nil)
    (bodyRows A pureFirst) (children := fun _ => body.1) (fun _ => body.2) <|
    .ret (nextRuntime [] (carried A)) (.cons (newest .head []) .nil)⟩

def Loop.compile (s : Loop Φ ε A) (pureFirst : Bool := true) :
    NestedTheta.Graph (Op Φ ε) (Threaded (carried A)) [] [Threaded (carried A)] (Threaded (carried A)) :=
  (s.code pureFirst).1.toGraph

def Loop.compileChecked (s : Loop Φ ε A) (pureFirst : Bool) :
    EntryChecked (a := carriedData A) (b := carriedData A) (s.compile pureFirst).toTerm :=
  (NestedTheta.Term.toTerm_toGraph _).symm ▸ (s.code pureFirst).2

section Model

variable {σ : Type u} [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- The typed activation used by the existing Elgot iteration theorem. -/
def Loop.step (s : Loop Φ ε A) (x : TyDen A) : StateT σ Part.{u} (TyDen A ⊕ TyDen A) := do
  let route ← callCase (ε := ε) s.decide x
  let y := PureRow.pureCall (σ := σ) s.value s.bottom x
  pure (Sum.map (fun _ => y) (fun _ => y) route)

def encodeExit (p : LabelDen [A] × σ) := point (exitValue p.1) p.2

def Loop.run (s : Loop Φ ε A) (base : Actions (τ := τ) (ε := ε) (σ := σ) Φ)
    (pureFirst : Bool) (fuel : Nat) (x : TyDen A) (initial : σ) :=
  NestedTheta.Partial.Executable.run (PureGamma.actions base) (s.compile pureFirst) fuel (point x initial)

end Model

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureTheta
