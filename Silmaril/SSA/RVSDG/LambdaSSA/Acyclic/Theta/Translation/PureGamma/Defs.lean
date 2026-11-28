module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PurePrefix.Defs

/-! # Checked pure and ordered bindings in a selected γ child -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma

open Isotope.LambdaSSA (Region Ren At)
open Isotope.LetIter.ProofRelevant.Semantics
open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Data Threaded runtimePort nextRuntime)
open LinearChain.Wiring (newest)
open NestedTheta.ExplicitRuntime.Splice (weaken)
open NestedTheta.ExplicitRuntime.PurePrefix (Code EntryChecked)
open Sequential
open PureRow (Segment EarlyRows LateRows Output)
open PurePrefix (orderedCall)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A P B C : τ}

/-- A data-only instruction label contains its bottom-effect proof. -/
inductive ValueOp (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] : Dialect.{u,u} τ PUnit where
  | call {I O : τ} (p : TwoBlock.Instruction Φ I O) (h : (instrEff p.op : ε) = ⊥) :
      ValueOp Φ ε (carried I) (carried O)

abbrev Op (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] :=
  NestedTheta.ExplicitRuntime.PurePrefix.Op (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)

abbrev resultsData (P C : τ) : Data [.value P, .value C] := .value (carriedData C)

def rows (P B C : τ) (pureFirst : Bool) := if pureFirst then EarlyRows P B C else LateRows P B C

def armRows (P B C : τ) (pureFirst : Bool) : Fin 2 → List (Ports (OrderedRuntime.Structured.Ty τ)) :=
  Fin.cases (rows P B C pureFirst) (fun _ => rows P B C true)

/-- The second ordered instruction always takes the first instruction's
returned token. The result returns the second instruction's token. -/
def arm (s : Segment Φ ε A P B C) (pureFirst : Bool) :
    Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)
      (carriedData A) (resultsData P C) (.arg (runtimePort (carried A))) (rows P B C pureFirst) :=
  let entry := Origin.arg (past := []) (runtimePort (carried A))
  let value := ValueOp.call s.value s.bottom
  let arg {past : List (Ports (OrderedRuntime.Structured.Ty τ))} : Wires (Threaded (carried A)) past (carried A) :=
    .cons (.arg .head) .nil
  match pureFirst with
  | true =>
    let previous := [carried P]
    let afterFirst := previous ++ [Threaded (carried B)]
    ⟨_, .pure entry (carriedData _) (carriedData _) value arg <|
      .primitive (weaken (carried P) entry) (carriedData _) (carriedData _) (orderedCall s.first) arg <|
      .primitive (nextRuntime previous (carried B)) (carriedData _) (carriedData _) (orderedCall s.second) arg <|
      .ret (nextRuntime afterFirst (carried C))
        (.cons (.output (0 : Fin 3) .head) (.cons (newest .head afterFirst) .nil))⟩
  | false =>
    let previous := [Threaded (carried B)]
    let live := nextRuntime [] (carried B)
    let afterValue := previous ++ [carried P]
    ⟨_, .primitive entry (carriedData _) (carriedData _) (orderedCall s.first) arg <|
      .pure live (carriedData _) (carriedData _) value arg <|
      .primitive (weaken (carried P) live) (carriedData _) (carriedData _) (orderedCall s.second) arg <|
      .ret (nextRuntime afterValue (carried C))
        (.cons (.output (1 : Fin 3) .head) (.cons (newest .head afterValue) .nil))⟩

abbrev Input (A : τ) : Ports (OrderedRuntime.Structured.Ty τ) := .control 2 :: carried A

abbrev inputData (A : τ) : Data (Input A) := .control (carriedData A)

abbrev Choice (A : τ) := Silmaril.coprod A A

/-- The flat case binds the selected entry payload. Arm instructions have
access to that payload, with the original sum discarded by renaming. -/
structure Branch (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A P B C : τ) where
  left : Segment Φ ε A P B C
  right : Segment Φ ε A P B C

omit [HasTy Φ τ] [HasEff Φ ε] [Bot ε] in
theorem armEntry : Ren [A] [A, Choice A] id := by
  intro i T h
  cases i with
  | zero => exact h
  | succ n => simp [At] at h

def Branch.region (s : Branch Φ ε A P B C) : Region Φ :=
  .case (.var 0) (s.left.region.renameVars id) (s.right.region.renameVars id)

theorem Branch.typing (s : Branch Φ ε A P B C) :
    Region.HasType [Choice A] s.region [Silmaril.product P C] :=
  .case (.var rfl) (s.left.typing.renameVars armEntry) (s.right.typing.renameVars armEntry)

/-- The first γ arm admits either placement of the pure row. Both child
boundaries receive the incoming token and supply the γ result token. -/
def Branch.code (s : Branch Φ ε A P B C) (pureFirst : Bool) :
    Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)
      (inputData A) (resultsData P C) (.arg (runtimePort (Input A))) [Output P C] :=
  let arms := Fin.cases (motive := fun i =>
      Code (past := []) (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) (ValueOp Φ ε)
        (carriedData A) (resultsData P C) (.arg (runtimePort (carried A))) (armRows P B C pureFirst i))
    (arm s.left pureFirst) (fun _ => arm s.right true)
  ⟨_, .gamma 0 (.arg .head) (.arg (runtimePort (Input A))) (carriedData _) (resultsData P C)
    (.cons (.arg (.tail .head)) .nil) (armRows P B C pureFirst)
    (children := fun i => (arms i).1) (fun i => (arms i).2) <|
    .ret (nextRuntime [] [.value P, .value C])
      (.cons (newest .head []) (.cons (newest (.tail .head) []) .nil))⟩

def Branch.compile (s : Branch Φ ε A P B C) (pureFirst : Bool := true) := (s.code pureFirst).1.toGraph

def Branch.compileChecked (s : Branch Φ ε A P B C) (pureFirst : Bool) :
    EntryChecked (a := inputData A) (b := resultsData P C) (s.compile pureFirst).toTerm :=
  (NestedTheta.Term.toTerm_toGraph _).symm ▸ (s.code pureFirst).2

def valueCode : NestedTheta.Equality.OpcodeCode (ValueOp (τ := τ) Φ ε) where
  Key := Φ
  encode | .call p _ => p.op
  injective := by
    intro _ _ x y same
    cases x with
    | call p _ =>
      cases y with
      | call q _ =>
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

abbrev OrderedModel := Wires.wireModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)

def evalValue : NestedTheta.ExplicitRuntime.PurePrefix.Total (OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ))
    (ValueOp (τ := τ) Φ ε)
  | _, _, .call p h, .cons x .nil => .cons (PureRow.pureCall (σ := σ) p h x) .nil

abbrev model :=
  NestedTheta.ExplicitRuntime.PurePrefix.model (OrderedModel (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)) evalValue

def actions (base : Actions (τ := τ) (ε := ε) (σ := σ) Φ) :
    NestedTheta.Partial.Executable.Actions (model (τ := τ) (Φ := Φ) (ε := ε) (σ := σ)) :=
  NestedTheta.ExplicitRuntime.PurePrefix.actions _ _ base

def entry (choice : TyDen (Choice A)) (token : σ) :
    Tuple (OrderedRuntime.Structured.RuntimeValues (TyDen (τ := τ)) σ) (Threaded (Input A)) :=
  match TypeModel.coprodEquiv A A choice with
  | .inl x => .cons ⟨0⟩ (OrderedTheta.point x token)
  | .inr x => .cons ⟨1⟩ (OrderedTheta.point x token)

end Model

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Translation.PureGamma
