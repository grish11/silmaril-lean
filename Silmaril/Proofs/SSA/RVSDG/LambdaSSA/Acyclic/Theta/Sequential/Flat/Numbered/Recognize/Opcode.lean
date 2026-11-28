module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Opcode.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Proofs

open OrderedRuntime.Structured (Instruction Data Threaded)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

omit [TypeFormers τ] in
private theorem op_eq {A B : τ} (p q : TwoBlock.Instruction Φ A B) (h : p.op = q.op) : p = q := by
  cases p
  cases q
  cases h
  rfl

private theorem route_heq {S A T B : τ} (p : Acyclic.Input S A) (q : Acyclic.Input T B)
    (h : routeCode p = routeCode q) : HEq p q := by
  cases p <;> cases q <;> simp only [routeCode, RouteCode.left.injEq, RouteCode.right.injEq,
    RouteCode.direct.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h; rfl

private theorem route_eq {S A : τ} (p q : Acyclic.Input S A) (h : routeCode p = routeCode q) : p = q :=
  eq_of_heq (route_heq p q h)

private structure PackedInstruction (Φ : Type u) [HasTy Φ τ] where
  ins : Ports (OrderedRuntime.Structured.Ty τ)
  outs : Ports (OrderedRuntime.Structured.Ty τ)
  inData : Data ins
  outData : Data outs
  op : Instruction (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) ins outs

private theorem instruction_packed {i o i' o' : Ports (OrderedRuntime.Structured.Ty τ)}
    (a : Data i) (b : Data o) (a' : Data i') (b' : Data o')
    (p : Instruction (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) i o)
    (q : Instruction (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) i' o')
    (h : instructionKey p = instructionKey q) :
    (PackedInstruction.mk i o a b p) = PackedInstruction.mk i' o' a' b' q := by
  cases p
  case' pure x => cases x
  case' effect x =>
    cases x
    case' nested x => cases x
    case' loop x =>
      cases x
      case' acyclic x => cases x
  all_goals
    cases q
    case' pure y => cases y
    case' effect y =>
      cases y
      case' nested y => cases y
      case' loop y =>
        cases y
        case' acyclic y => cases y
  all_goals simp [instructionKey, pureKey, effectKey, loopKey, acyclicKey, NestedFeedback.Reverse.effectKey] at h
  all_goals
    first
    | obtain ⟨rfl, rfl, rfl, rfl, route, op⟩ := h
      rw [route_eq _ _ route, op_eq _ _ op]
    | obtain ⟨rfl, rfl, rfl, route, op⟩ := h
      rw [route_eq _ _ route, op_eq _ _ op]
    | obtain ⟨rfl, rfl, rfl, rfl, op⟩ := h
      rw [op_eq _ _ op]
    | obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl
    | obtain ⟨rfl, rfl, op⟩ := h
      rw [op_eq _ _ op]
    | obtain ⟨rfl, op⟩ := h
      rw [op_eq _ _ op]

private def PackedInstruction.toOpcode (p : PackedInstruction (τ := τ) Φ) :
    Σ i o : Ports (OrderedRuntime.Structured.Ty τ), Wires.Op Φ i o :=
  ⟨Threaded p.ins, Threaded p.outs, .ordered p.inData p.outData p.op⟩

private theorem opcode_packed {i o i' o' : Ports (OrderedRuntime.Structured.Ty τ)}
    (x : Wires.Op Φ i o) (y : Wires.Op Φ i' o') (equal : opcodeKey x = opcodeKey y) :
    (⟨i, o, x⟩ : Σ i o : Ports (OrderedRuntime.Structured.Ty τ), Wires.Op Φ i o) = ⟨i', o', y⟩ := by
  cases x with
  | ordered a b x =>
    cases y with
    | ordered a' b' y =>
      exact congrArg PackedInstruction.toOpcode (instruction_packed a b a' b' x y equal)

theorem opcode_injective {i o : Ports (OrderedRuntime.Structured.Ty τ)}
    (p q : Wires.Op Φ i o) (h : opcodeKey p = opcodeKey q) : p = q :=
  eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj (opcode_packed p q h)).2)).2

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Proofs
