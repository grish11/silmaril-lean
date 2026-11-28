module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.Model.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Check.Defs

/-! # One independent pure row beside a state-token chain -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.PureRow

open Isotope.LambdaSSA (Tm Region)
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (LabelDen)
open OrderedTheta (carried point)
open OrderedRuntime.Structured (Threaded runtime withRuntime)

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
variable {A P B C : τ}

abbrev Wire (T : τ) := Threaded (carried T)

/-- A pure label carries proof of bottom effect. The other label is
interpreted through the explicit token even when its instruction is pure. -/
inductive Op (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] : Dialect.{u,u} τ PUnit where
  | pure {I O : τ} (p : TwoBlock.Instruction Φ I O) (h : (instrEff p.op : ε) = ⊥) :
      Op Φ ε (carried I) (carried O)
  | ordered {I O : τ} (p : TwoBlock.Instruction Φ I O) : Op Φ ε (Wire I) (Wire O)

/-- All three rows read the entry value. Only the second ordered action
reads the first one's result token. The pure value is returned separately. -/
structure Segment (Φ ε : Type u) [HasTy Φ τ] [HasEff Φ ε] [Bot ε] (A P B C : τ) where
  value : TwoBlock.Instruction Φ A P
  bottom : (instrEff value.op : ε) = ⊥
  first : TwoBlock.Instruction Φ A B
  second : TwoBlock.Instruction Φ A C

/-- The actual flat LambdaSSA block, with one typed external exit. -/
def Segment.region (s : Segment Φ ε A P B C) : Region Φ :=
  .let₁ (.op s.value.op (.var 0)) <|
    .let₁ (.op s.first.op (.var 1)) <|
      .let₁ (.op s.second.op (.var 2)) <|
        .br 0 (.pair (.var 2) (.var 0))

theorem typingAt (p : TwoBlock.Instruction Φ A C) {Γ : List τ} {i : Nat} (hi : Γ[i]? = some A) :
    Tm.HasType Γ (.op p.op (.var i)) C :=
  p.typingAt hi

theorem Segment.typing (s : Segment Φ ε A P B C) :
    Region.HasType [A] s.region [Silmaril.product P C] :=
  .let₁ (typingAt s.value rfl) (.let₁ (typingAt s.first rfl) (.let₁ (typingAt s.second rfl)
    (.br rfl (.pair (.var rfl) (.var rfl)))))

abbrev Output (P C : τ) : Ports (OrderedRuntime.Structured.Ty τ) := Threaded [.value P, .value C]
abbrev EarlyRows (P B C : τ) : List (Ports (OrderedRuntime.Structured.Ty τ)) := [carried P, Wire B, Wire C]
abbrev LateRows (P B C : τ) : List (Ports (OrderedRuntime.Structured.Ty τ)) := [Wire B, carried P, Wire C]

def dataRow (s : Segment Φ ε A P B C) (past : List (Ports (OrderedRuntime.Structured.Ty τ))) :
    NestedTheta.Node (Op Φ ε) (Wire A) past (carried P) :=
  ⟨_, .base (.simple (.pure s.value s.bottom)), .cons (.arg .head) .nil, fun j => j.elim0⟩

def orderedRow (p : TwoBlock.Instruction Φ A C) {past : List (Ports (OrderedRuntime.Structured.Ty τ))}
    (token : Origin (Wire A) past runtime) : NestedTheta.Node (Op Φ ε) (Wire A) past (Wire C) :=
  ⟨_, .base (.simple (.ordered p)), withRuntime token (.cons (.arg .head) .nil), fun j => j.elim0⟩

def Segment.early (s : Segment Φ ε A P B C) :
    NestedTheta.Term (Op Φ ε) (Wire A) [] (EarlyRows P B C) (Output P C) :=
  .bind (dataRow s []) (fun j => j.elim0) <|
    .bind (orderedRow (ε := ε) s.first (.arg (.tail .head))) (fun j => j.elim0) <|
      .bind (orderedRow (ε := ε) s.second (.output (1 : Fin 2) (.tail .head))) (fun j => j.elim0) <|
        .ret (.cons (.output (0 : Fin 3) .head)
          (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil)))

def Segment.late (s : Segment Φ ε A P B C) :
    NestedTheta.Term (Op Φ ε) (Wire A) [] (LateRows P B C) (Output P C) :=
  .bind (orderedRow (ε := ε) s.first (.arg (.tail .head))) (fun j => j.elim0) <|
    .bind (dataRow s [Wire B]) (fun j => j.elim0) <|
      .bind (orderedRow (ε := ε) s.second (.output (0 : Fin 2) (.tail .head))) (fun j => j.elim0) <|
        .ret (.cons (.output (1 : Fin 3) .head)
          (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil)))

/-- The source opcode and its state-wire mode identify a typed row label. -/
def opcodeCode : NestedTheta.Equality.OpcodeCode (Op (τ := τ) Φ ε) where
  Key := Sum Φ Φ
  encode
    | .pure p _ => .inl p.op
    | .ordered p => .inr p.op
  injective := by
    intro ins outs x y same
    cases x with
    | pure p hp =>
      cases y with
      | pure q hq =>
        have eq : p = q := by
          cases p
          cases q
          cases Sum.inl.inj same
          rfl
        cases eq
        rfl
    | ordered p =>
      cases y with
      | ordered q =>
        have eq : p = q := by
          cases p
          cases q
          cases Sum.inr.inj same
          rfl
        cases eq
        rfl

section Model

variable {σ : Type u} [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
  [InstructionModel Φ τ ε (StateT σ Part.{u})]

/-- Use the value interpretation supplied for the bottom-effect instruction. -/
def pureCall (p : TwoBlock.Instruction Φ A P) (h : (instrEff p.op : ε) = ⊥) (x : TyDen A) : TyDen P :=
  p.output ▸ denotePureInstr (m := StateT σ Part.{u}) p.op h (p.input.symm ▸ x)

def model : NestedTheta.Partial.Model.{u,u,u} (Op (τ := τ) Φ ε) where
  value := TyDen
  snapshot _ := σ
  primitive
    | .pure p h, .cons x .nil => Part.some (.cons (pureCall (σ := σ) p h x) .nil)
    | .ordered p, .cons x (.cons token .nil) =>
      Part.map (fun (y, next) => point y next) ((TwoBlock.call (ε := ε) (m := StateT σ Part.{u}) p x).run token)

def output (p : TyDen P) (c : TyDen C) (token : σ) :
    Tuple (OrderedRuntime.Structured.RuntimeValues (TyDen (τ := τ)) σ) (Output P C) :=
  .cons p (.cons c (.cons token .nil))

def encodeExit : LabelDen [Silmaril.product P C] × σ →
    Tuple (OrderedRuntime.Structured.RuntimeValues (TyDen (τ := τ)) σ) (Output P C)
  | (.inl pair, token) => let values := TypeModel.productEquiv P C pair; output values.1 values.2 token
  | (.inr dead, _) => PEmpty.elim dead

end Model

end Silmaril.SSA.RVSDG.LambdaSSA.PureRow
