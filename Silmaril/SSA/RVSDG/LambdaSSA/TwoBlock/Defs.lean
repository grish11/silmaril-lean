module

public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms

/-! # A typed header/body loop and its ordered RVSDG translation -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock

open Isotope.LambdaSSA (Tm Region)

universe u

set_option backward.isDefEq.respectTransparency false
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

/-- A typed application to the current block argument. -/
structure Instruction (Φ : Type u) [HasTy Φ τ] (src dst : τ) where
  op : Φ
  input : instrSrc op = src
  output : instrTrg op = dst

structure Blocks (Φ : Type u) [HasTy Φ τ] (A B : τ) where
  header : Instruction Φ A (Silmaril.coprod A B)
  body : Instruction Φ B A

variable {A B C : τ}

theorem Instruction.typingAt (op : Instruction Φ A C) {Γ : List τ} {i : Nat}
    (h : Γ[i]? = some A) : Tm.HasType Γ (.op op.op (.var i)) C :=
  Eq.ndrec (motive := fun t => Tm.HasType Γ (.op op.op (.var i)) t)
    (.op (.var (h.trans (congrArg some op.input.symm)))) op.output

theorem Instruction.typing (op : Instruction Φ A C) (Γ : List τ) :
    Tm.HasType (A :: Γ) (.op op.op (.var 0)) C := op.typingAt rfl

/-- Header label 0 takes A, body label 1 takes B, and outward label 2 takes A. -/
def header (op : Φ) : Region Φ :=
  .case (.op op (.var 0)) (.br 2 (.var 0)) (.br 1 (.var 0))

def body (op : Φ) : Region Φ :=
  .br 0 (.op op (.var 0))

def localTypes (A B : τ) : Fin 2 → τ :=
  Fin.cases A (fun _ => B)

def blocks (headOp bodyOp : Φ) : Fin 2 → Region Φ :=
  Fin.cases (header headOp) (fun _ => body bodyOp)

def region (headOp bodyOp : Φ) : Region Φ :=
  .cfg (.br 0 (.var 0)) 2 (blocks headOp bodyOp)

theorem headerTyping (s : Blocks Φ A B) :
    Region.HasType [A, A] (header s.header.op) [A, B, A] :=
  .case (s.header.typing [A]) (.br rfl (.var rfl)) (.br rfl (.var rfl))

theorem bodyTyping (s : Blocks Φ A B) :
    Region.HasType [B, A] (body s.body.op) [A, B, A] :=
  .br rfl (s.body.typing [A])

theorem blockTyping (s : Blocks Φ A B) (i : Fin 2) :
    Region.HasType (localTypes A B i :: [A]) (blocks s.header.op s.body.op i) [A, B, A] :=
  Fin.cases (motive := fun j => Region.HasType (localTypes A B j :: [A])
    (blocks s.header.op s.body.op j) [A, B, A])
    (headerTyping s) (fun _ => bodyTyping s) i

theorem regionTyping (s : Blocks Φ A B) : Region.HasType [A] (region s.header.op s.body.op) [A] :=
  .cfg (localTypes A B) (.br rfl (.var rfl)) (blockTyping s)

open OrderedTheta (carried results)

abbrev headerPorts (A B : τ) : Ports (OrderedRuntime.Structured.Ty τ) := [.control 2, .value (Silmaril.coprod A B)]
abbrev armPorts (A B : τ) : Ports (OrderedRuntime.Structured.Ty τ) := [.value A, .value (Silmaril.coprod A B)]

inductive Pure (τ : Type u) [TypeFormers τ] : Dialect.{u, u} τ PUnit where
  | exit {A B : τ} : Pure τ (armPorts A B) (results A)

inductive Effect (Φ : Type u) [HasTy Φ τ] : Dialect.{u, u} τ PUnit where
  | header {A B : τ} : Instruction Φ A (Silmaril.coprod A B) → Effect Φ (carried A) (headerPorts A B)
  | body {A B : τ} : Instruction Φ B A → Effect Φ (armPorts A B) (results A)

abbrev Op (Φ : Type u) [HasTy Φ τ] := OrderedRuntime.Structured.Instruction (Pure τ) (Effect Φ)

def arm (op : Op Φ (armPorts A B) (results A)) :
    NestedTheta.Term (Op Φ) (armPorts A B) [] [results A] (results A) :=
  .bind ⟨armPorts A B, .base (.simple op), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    fun i => i.elim0⟩ (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

def thetaBody (s : Blocks Φ A B) : NestedTheta.Term (Op Φ) (carried A) []
    [headerPorts A B, results A] (results A) :=
  let headerNode : NestedTheta.Node (Op Φ) (carried A) [] (headerPorts A B) :=
    ⟨carried A, .base (.simple (.effect (.header s.header))), .cons (.arg .head) .nil, fun i => i.elim0⟩
  let selectNode : NestedTheta.Node (Op Φ) (carried A) [headerPorts A B] (results A) :=
    ⟨.control 2 :: armPorts A B, .base (.gamma 0),
      .cons (.output (0 : Fin 1) .head)
        (.cons (.arg .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)),
      fun _ => [results A]⟩
  .bind headerNode (fun i => i.elim0) <|
    .bind selectNode (Fin.cases (arm (.pure Pure.exit)) (fun _ => arm (.effect (.body s.body)))) <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))

abbrev Loop (Φ : Type u) [HasTy Φ τ] (A : τ) :=
  NestedTheta.Graph (Op Φ) (carried A) [] [carried A] (carried A)

def loopTerm (s : Blocks Φ A B) : NestedTheta.Term (Op Φ) (carried A) [] [carried A] (carried A) :=
  .bind (NestedTheta.thetaVertex [headerPorts A B, results A])
    (fun _ => thetaBody s) (.ret (NestedTheta.thetaResults (carried A)))

def graph (s : Blocks Φ A B) : Loop Φ A := (loopTerm s).toGraph

inductive SSAForm (A B : τ) : Region Φ → Type u where
  | loop (s : Blocks Φ A B) : SSAForm A B (region s.header.op s.body.op)

inductive RVForm (A B : τ) : Loop Φ A → Type u where
  | loop (s : Blocks Φ A B) : RVForm A B (graph s)

/-- The instruction witnesses and fixed typed wires determine the relation. -/
inductive Related (A B : τ) : Region Φ → Loop Φ A → Type u where
  | loop (s : Blocks Φ A B) : Related A B (region s.header.op s.body.op) (graph s)

def lower {r : Region Φ} (h : SSAForm A B r) : Σ g : Loop Φ A, Related A B r g :=
  match h with
  | .loop s => ⟨graph s, .loop s⟩

def raise {g : Loop Φ A} (h : RVForm A B g) : Σ r : Region Φ, Related A B r g :=
  match h with
  | .loop s => ⟨region s.header.op s.body.op, .loop s⟩

def Related.instructions {r : Region Φ} {g : Loop Φ A} (h : Related A B r g) : Blocks Φ A B :=
  match h with
  | .loop s => s

theorem Related.typing {r : Region Φ} {g : Loop Φ A} (h : Related A B r g) :
    Region.HasType [A] r [A] := by
  cases h with
  | loop s => exact regionTyping s

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock
