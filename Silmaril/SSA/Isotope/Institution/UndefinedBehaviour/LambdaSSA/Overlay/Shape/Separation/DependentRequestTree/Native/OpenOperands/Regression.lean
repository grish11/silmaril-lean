module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent (pack)
open Category.FiniteIteration.CFG.Dependent.Native (withExitUB)
open LambdaSSA.Region (packedExitType)
open TwoRequest (Tag)

private inductive Op where
  | flip
  | test
  deriving DecidableEq

private abbrev Bit : Syntax.Ty := .coprod .unit .unit

private abbrev replies : Op → List Syntax.Ty
  | .flip => [Bit]
  | .test => [.unit]

private instance : HasTy Op Syntax.Ty := ⟨fun _ => Bit, fun f => packedExitType (replies f)⟩

private abbrev sig : RequestSignature Op := ⟨replies, fun _ => rfl⟩
private abbrev Packets : List Syntax.Ty := [Bit, Bit, .unit]

/-- The same reply position always goes to block one. The operand there
can read either the new reply or the original caller packet. -/
private def table (caller : Bool) (exit : Tag) : Table sig Packets where
  entry := (0 : Fin 3)
  row := Fin.cases (motive := fun i : Fin 3 => Row sig Packets [Packets.get i, Bit])
    (.request .flip (Syntax.Expr.var (Γ := [Bit, Bit]) (0 : Fin 2)) (fun _ => (1 : Fin 3)) (fun (j : Fin 1) => by
      obtain rfl := Fin.eq_zero j
      rfl))
    (Fin.cases (motive := fun i : Fin 2 => Row sig Packets [Packets.get i.succ, Bit])
      (.request .test (if caller then Syntax.Expr.var (Γ := [Bit, Bit]) (1 : Fin 2) else Syntax.Expr.var (Γ := [Bit, Bit]) (0 : Fin 2))
        (fun _ => (2 : Fin 3)) (fun (j : Fin 1) => by
          obtain rfl := Fin.eq_zero j
          rfl))
      (fun _ => .exit exit))
  selected i := i == (1 : Fin 2)

private def left : Syntax.Payload Bit := ⟨.inl .unit, .inl .unit⟩
private def right : Syntax.Payload Bit := ⟨.inr .unit, .inr .unit⟩
private def unitPayload : Syntax.Payload (.unit : Syntax.Ty) := ⟨.unit, .unit⟩

private def primitives : Syntax.Primitives Op 3 := fun f a s =>
  match f with
  | .flip =>
    if s = 0 then
      let flipped := match a.val with
        | .inl _ => right
        | _ => left
      .ret (pack (L := replies .flip) ⟨(0 : Fin 1), flipped⟩) 1
    else .diverge
  | .test =>
    if s = 1 then
      match a.val with
      | .inr _ => .ret (pack (L := replies .test) ⟨(0 : Fin 1), unitPayload⟩) 2
      | _ => .fault 2
    else .diverge

private abbrev source := table false 0
private abbrev marked := table false 1
private abbrev readsCaller := table true 0

example : source.extract? readsCaller.native left = none := rfl

example : ((source.extract? source.native left).map fun t => t.execute primitives (0 : Fin 3)) =
    some (.ret 0 2) := rfl

example : ((source.extract? source.native right).map fun t => t.execute primitives (0 : Fin 3)) =
    some (.fault 2) := rfl

example : Shape.denote (withExitUB source.native source.selected)
    (Syntax.model primitives (source.bindings left)) 0 =
      WithTop.some {Outcome.ret (0 : Fin 2) Value.unit (2 : Fin 3)} :=
  (source.observe (raw := source.native) rfl left primitives 0).symm

example : Shape.denote (withExitUB readsCaller.native readsCaller.selected)
    (Syntax.model primitives (readsCaller.bindings left)) 0 =
      WithTop.some {Outcome.fault (2 : Fin 3)} :=
  (readsCaller.observe (raw := readsCaller.native) rfl left primitives 0).symm

example : Shape.denote (withExitUB marked.native marked.selected)
    (Syntax.model primitives (marked.bindings left)) 0 = ⊤ :=
  (marked.observe (raw := marked.native) rfl left primitives 0).symm

example : Shape.denote (withExitUB marked.native marked.selected)
    (Syntax.model primitives (marked.bindings right)) 0 =
      WithTop.some {Outcome.fault (2 : Fin 3)} :=
  (marked.observe (raw := marked.native) rfl right primitives 0).symm

example : Shape.denote (withExitUB marked.native marked.selected)
    (Syntax.model primitives (marked.bindings left)) (2 : Fin 3) =
      WithTop.some {Outcome.diverge} :=
  (marked.observe (raw := marked.native) rfl left primitives 2).symm

private abbrev sourceTree := source.extract rfl left
private abbrev callerTree := readsCaller.extract rfl left
private abbrev markedTree := marked.extract rfl left

/-- Both trees have the same entry query. Its single reply position carries
the right bit, so the next arguments differ even though the opcode matches. -/
private def probe : Prefix sig.replies 1 :=
  .step .flip left.val 0 right (.stop (some (.test, right.val)))

example : sourceTree.Follows probe := .step (.stop _ _)
example : callerTree.Follows probe := .step (.stop _ _)

example : Shape.denote (withExitUB source.native source.selected)
    (Syntax.model (sig.primitives probe.handler) (source.bindings left)) 0 =
      WithTop.some {Outcome.fault (1 : Fin 2)} :=
  (source.observe_extract (raw := source.native) (tree := sourceTree) rfl _ 0).symm

example : Shape.denote (withExitUB readsCaller.native readsCaller.selected)
    (Syntax.model (sig.primitives probe.handler) (readsCaller.bindings left)) 0 =
      WithTop.some {Outcome.diverge} :=
  (readsCaller.observe_extract (raw := readsCaller.native) (tree := callerTree) rfl _ 0).symm

private def otherReply : Prefix sig.replies 1 :=
  .step .flip left.val 0 left (.stop (some (.test, left.val)))

example : sourceTree.execute (sig.primitives otherReply.handler) 0 = .fault 1 := rfl
example : callerTree.execute (sig.primitives otherReply.handler) 0 = .fault 1 := rfl

private theorem changedArgument : ¬ sourceTree.Refines callerTree := by
  intro h
  have results := Tree.refines_execute h (sig.primitives probe.handler) 0
  change (Result.fault (1 : Fin 2) : Result 2 2).refines .diverge at results
  simp [Result.refines] at results

example :
    ∃ (n : Nat) (witness : Prefix sig.replies n),
      n ≤ 3 ∧ sourceTree.Follows witness ∧ callerTree.Follows witness ∧
      ¬ Shape.denote (withExitUB source.native source.selected)
          (Syntax.model (sig.primitives witness.handler) (source.bindings left)) 0 ≤
        Shape.denote (withExitUB readsCaller.native readsCaller.selected)
          (Syntax.model (sig.primitives witness.handler) (readsCaller.bindings left)) 0 :=
  Table.exists_prefix_countermodel (g₀ := source) (g₁ := readsCaller)
    (raw₀ := source.native) (raw₁ := readsCaller.native) rfl rfl rfl changedArgument

private theorem return_below_marked : sourceTree.Refines markedTree := by
  refine ⟨rfl, rfl, fun i a => ?_⟩
  obtain rfl := Fin.eq_zero i
  refine ⟨rfl, rfl, fun j b => ?_⟩
  obtain rfl := Fin.eq_zero j
  exact Or.inl rfl

example (n : Nat) (prim : Syntax.Primitives Op n) (s : Fin n) :
    Shape.denote (withExitUB source.native source.selected) (Syntax.model prim (source.bindings left)) s ≤
      Shape.denote (withExitUB marked.native marked.selected) (Syntax.model prim (marked.bindings left)) s :=
  (Table.refines_iff (g₀ := source) (g₁ := marked) (raw₀ := source.native)
    (raw₁ := marked.native) (input := left) (p := sourceTree) (q := markedTree) rfl rfl rfl).mpr
      return_below_marked n prim s

example : ¬ markedTree.Refines sourceTree := by
  intro related
  have results := Tree.refines_execute related primitives 0
  change (Result.ub : Result 2 3).refines (.ret 0 2) at results
  simp [Result.refines] at results

private abbrev otherExit : Table sig Packets := { marked with selected := fun _ => false }

example : ¬ sourceTree.Refines (otherExit.extract rfl left) := by
  intro related
  have results := Tree.refines_execute related primitives 0
  change (Result.ret 0 (2 : Fin 3) : Result 2 3).refines (.ret 1 2) at results
  simp [Result.refines] at results

example : sourceTree.Refines (.stop .ub) := trivial
example : ¬ (Tree.stop .ub).Refines markedTree := not_false

private def packets : (f : Op) → List (CFG.Dependent.Packet (sig.replies f))
  | .flip => [⟨0, left⟩, ⟨0, right⟩]
  | .test => [⟨0, unitPayload⟩]

private def enumeration : ReplyEnumeration sig where
  packets := packets
  complete f packet := by
    cases f
    · obtain ⟨i, value, typed⟩ := packet
      obtain rfl := Fin.eq_zero i
      cases typed with
      | inl typed =>
        cases typed
        exact List.Mem.head _
      | inr typed =>
        cases typed
        exact List.Mem.tail _ (List.Mem.head _)
    · obtain ⟨i, value, typed⟩ := packet
      obtain rfl := Fin.eq_zero i
      cases typed
      exact List.Mem.head _

private def checkFlipReply (p q : Tree sig) (a : Syntax.Payload Bit) : Bool :=
  match p, q with
  | .ask .flip _ arms, .ask .flip _ next => ((arms 0 a).compare enumeration (next 0 a)).accepted
  | _, _ => false

-- Both payloads occur at tag zero in this order. Only the later one fails.
example : checkFlipReply sourceTree callerTree left = true := rfl
example : checkFlipReply sourceTree callerTree right = false := rfl

example : source.compare? readsCaller enumeration source.native readsCaller.native rfl left =
    some (.counterexample 1 probe) := rfl

example : source.checkRefinement? readsCaller enumeration source.native readsCaller.native rfl left =
    some false := rfl

example : source.checkRefinement? marked enumeration source.native marked.native rfl left = some true := rfl

example : marked.checkRefinement? source enumeration marked.native source.native rfl left = some false := rfl

example : source.checkRefinement? readsCaller enumeration readsCaller.native readsCaller.native rfl left =
    none := rfl

example : 1 ≤ 3 ∧ sourceTree.Follows probe ∧ callerTree.Follows probe ∧
    ¬ Shape.denote (withExitUB source.native source.selected)
        (Syntax.model (sig.primitives probe.handler) (source.bindings left)) 0 ≤
      Shape.denote (withExitUB readsCaller.native readsCaller.selected)
        (Syntax.model (sig.primitives probe.handler) (readsCaller.bindings left)) 0 :=
  Table.compare_counterexample (g₀ := source) (g₁ := readsCaller) (replies := enumeration)
    (raw₀ := source.native) (raw₁ := readsCaller.native) rfl rfl rfl rfl

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Table.checkRefinement_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Table.checkRefinement_iff

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Table.refines_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Table.refines_iff

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Table.observe_extract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Table.observe_extract

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
