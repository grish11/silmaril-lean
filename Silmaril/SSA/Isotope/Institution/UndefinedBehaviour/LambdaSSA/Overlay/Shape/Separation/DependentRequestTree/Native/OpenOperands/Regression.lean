module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Refinement.Checker.Interface.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent (Packet pack)
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

/-- The same reply position always goes to block one. Its operand can use
either the incoming reply or the original caller packet. -/
private def table (arg : Syntax.Expr [Bit, Bit] Bit) (exit : Tag) : Table sig Packets where
  entry := (0 : Fin 3)
  row := Fin.cases (motive := fun i : Fin 3 => Row sig Packets [Packets.get i, Bit])
    (.request .flip (Syntax.Expr.var (Γ := [Bit, Bit]) (0 : Fin 2)) (fun _ => (1 : Fin 3)) (fun (j : Fin 1) => by
      obtain rfl := Fin.eq_zero j
      rfl))
    (Fin.cases (motive := fun i : Fin 2 => Row sig Packets [Packets.get i.succ, Bit])
      (.request .test arg (fun _ => (2 : Fin 3)) (fun (j : Fin 1) => by
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

private abbrev source := table (.var 0) 0
private abbrev marked := table (.var 0) 1
private abbrev readsCaller := table (.var 1) 0

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

private def callers : CallerEnumeration Bit where
  packets := [left, right]
  complete input := by
    obtain ⟨value, typed⟩ := input
    cases typed with
    | inl typed =>
      cases typed
      exact List.Mem.head _
    | inr typed =>
      cases typed
      exact List.Mem.tail _ (List.Mem.head _)

private abbrev readsLiteral := table (.inl .unit) 0

-- The first caller packet agrees across every reply. The second changes the
-- query after a shared reply, so the returned prefix has one successful step.
example : readsCaller.checkRefinement? readsLiteral enumeration readsCaller.native readsLiteral.native
    rfl left = some true := rfl

example : readsCaller.checkRefinement? readsLiteral enumeration readsCaller.native readsLiteral.native
    rfl right = some false := rfl

private def laterCaller : InterfaceCounterexample sig Bit :=
  ⟨right, 1, .step .flip right.val 0 left (.stop (some (.test, right.val)))⟩

example : readsCaller.compareInterface? readsLiteral enumeration readsCaller.native readsLiteral.native
    rfl callers = some (.counterexample laterCaller) := rfl

example : ¬ Shape.denote (withExitUB readsCaller.native readsCaller.selected)
        (Syntax.model (sig.primitives laterCaller.probe.handler) (readsCaller.bindings right)) 0 ≤
      Shape.denote (withExitUB readsLiteral.native readsLiteral.selected)
        (Syntax.model (sig.primitives laterCaller.probe.handler) (readsLiteral.bindings right)) 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, failure⟩ :=
    Table.compareInterface_counterexample (g₀ := readsCaller) (g₁ := readsLiteral)
      (raw₀ := readsCaller.native) (raw₁ := readsLiteral.native)
      (replies := enumeration) (callers := callers) (w := laterCaller) rfl rfl
  exact failure

example : source.compareInterface? marked enumeration source.native marked.native rfl callers =
    some .refines := rfl

private def emptyTable (exit : Tag) : Table sig [.empty] where
  entry := 0
  row _ := .exit exit
  selected _ := false

private def emptyCallers : CallerEnumeration (.empty : Syntax.Ty) :=
  ⟨[], fun input => (Category.noEmptyPayload input).elim⟩

example : (emptyTable 0).compareInterface? (emptyTable 0) enumeration (emptyTable 0).native
    (emptyTable 0).native rfl emptyCallers = some .refines := rfl

example : (emptyTable 0).compareInterface? (emptyTable 0) enumeration (emptyTable 0).native
    (emptyTable 1).native rfl emptyCallers = none := rfl

private def loopRow (target : Fin Packets.length) (typed : Packets.get target = Bit)
    (operand : Syntax.Expr [Bit, Bit] Bit) : Row sig Packets [Bit, Bit] :=
  .request .flip operand (fun _ => target) fun j => by
    obtain rfl := Fin.eq_zero j
    exact typed

private def loopTable (operand : Syntax.Expr [Bit, Bit] Bit) : Table sig Packets where
  entry := 0
  row := Fin.cases (motive := fun i : Fin 3 => Row sig Packets [Packets.get i, Bit])
    (loopRow 0 rfl operand)
    (fun i => source.row i.succ)
  selected := source.selected

private abbrev backedge := loopTable (.var 0)
private abbrev literalLoop := loopTable (.inl .unit)

example : backedge.entryCheck = false := rfl

example : backedge.compareInterface? source enumeration backedge.native source.native rfl callers =
    none := rfl

private abbrev loopStart : Packet Packets := ⟨0, left⟩
private abbrev loopNext : Packet Packets := ⟨0, right⟩
private abbrev exitPoint : Packet Packets := ⟨2, unitPayload⟩

example : backedge.checkNative backedge.native = true := rfl

example : backedge.head? source.native left loopStart = none := rfl

private def silentBlock (i : Fin Packets.length) :
    CFG.Dependent.Native.Typed Op [Packets.get i, Bit] (Packets ++ TwoRequest.Exits) :=
  CFG.Dependent.Native.jump (Feedback.internal Packets TwoRequest.Exits i)
    (CFG.Dependent.internal_type i) (.var 0)

private def silentCycle : CFG.Dependent.Native.Typed Op [Bit] TwoRequest.Exits :=
  ⟨nativeFeedback backedge.entryRegion silentBlock, nativeFeedback_hasType backedge.entryRegion silentBlock⟩

example : backedge.head? silentCycle left loopStart = none := rfl

example : (backedge.head? backedge.native left loopStart).map (fun h => h.execute primitives 0) =
    some (.repeat loopNext 1) := rfl

example : (backedge.head left loopStart).successors enumeration = [loopStart, loopNext] := rfl

example : Feedback.Step (backedge.feedback left primitives) (blockPoint loopStart 0) (blockPoint loopNext 1) :=
  (backedge.feedback_step_iff left primitives loopStart 0 _).mpr ⟨loopNext, 1, rfl, rfl⟩

example : Shape.denote (withExitUB backedge.native backedge.selected)
    (Syntax.model primitives (backedge.bindings left)) 0 = WithTop.some {Outcome.diverge} :=
  (backedge.observe_entry backedge.native rfl left primitives 0).trans
    ((backedge.observe_step left primitives loopStart 0).trans
      (backedge.observe_step left primitives loopNext 1))

example : source.observeAt left primitives exitPoint 2 =
    WithTop.some {Outcome.ret (0 : Fin 2) Value.unit (2 : Fin 3)} :=
  source.observe_step left primitives exitPoint 2

example : otherExit.observeAt left primitives exitPoint 2 =
    WithTop.some {Outcome.ret (1 : Fin 2) Value.unit (2 : Fin 3)} :=
  otherExit.observe_step left primitives exitPoint 2

example : marked.observeAt left primitives exitPoint 2 = ⊤ :=
  marked.observe_step left primitives exitPoint 2

example : marked.observeAt left primitives ⟨(1 : Fin 3), left⟩ 1 =
    WithTop.some {Outcome.fault (2 : Fin 3)} :=
  marked.observe_step left primitives ⟨(1 : Fin 3), left⟩ 1

private def returnsForever : Syntax.Primitives Op 3 := fun f _ _ =>
  match f with
  | .flip => .ret (pack (L := replies .flip) ⟨0, right⟩) 1
  | .test => .diverge

/-- Every replay step is a successful request. The first one changes the
packet, and the typed successor then repeats indefinitely. -/
private theorem infiniteReplay :
    Feedback.Infinite (backedge.feedback left returnsForever) (blockPoint loopStart 0) := by
  refine ⟨fun j => Nat.casesOn j (blockPoint loopStart 0) (fun _ => blockPoint loopNext 1), rfl, ?_⟩
  intro j
  cases j with
  | zero =>
    exact (backedge.feedback_step_iff left returnsForever loopStart 0 _).mpr ⟨loopNext, 1, rfl, rfl⟩
  | succ j =>
    exact (backedge.feedback_step_iff left returnsForever loopNext 1 _).mpr ⟨loopNext, 1, rfl, rfl⟩

example : (Feedback.close (backedge.feedback left returnsForever) (blockPoint loopStart 0)).Ordinary .diverge := by
  apply Feedback.ordinary_close_iff.mpr
  refine ⟨?_, Or.inr ⟨rfl, infiniteReplay⟩⟩
  rintro ⟨q, _, top⟩
  cases q <;> exact WithTop.coe_ne_top top

private def loopPairs : List (Packet Packets × Packet Packets) :=
  [(loopStart, loopStart), (loopNext, loopNext)]

private def secondLoop : Table sig Packets where
  entry := 1
  row := Fin.cases (motive := fun i : Fin 3 => Row sig Packets [Packets.get i, Bit])
    (source.row 0)
    (Fin.cases (motive := fun i : Fin 2 => Row sig Packets [Packets.get i.succ, Bit])
      (loopRow 1 rfl (.var 0)) (fun _ => .exit 0))
  selected := source.selected

private def shiftedPairs : List (Packet Packets × Packet Packets) :=
  [(loopStart, ⟨1, left⟩), (loopNext, ⟨1, right⟩)]

example : backedge.checkProduct secondLoop left left enumeration shiftedPairs = true := rfl
example : backedge.checkProduct secondLoop left left enumeration [(loopStart, ⟨1, left⟩)] = false := rfl

example {n : Nat} (prim : Syntax.Primitives Op n) (s : Fin n) :
    Shape.denote (withExitUB backedge.native backedge.selected)
      (Syntax.model prim (backedge.bindings left)) s ≤
    Shape.denote (withExitUB secondLoop.native secondLoop.selected)
      (Syntax.model prim (secondLoop.bindings left)) s :=
  backedge.checkProduct_sound secondLoop backedge.native secondLoop.native rfl rfl
    left left enumeration shiftedPairs rfl prim s

-- The first listed reply loops within the proposed singleton relation.
-- The later payload at that same reply tag reaches the missing pair.
example : backedge.checkProduct literalLoop left left enumeration [(loopStart, loopStart)] = false := rfl

example : backedge.checkProduct literalLoop left left enumeration loopPairs = false := rfl

private def adverseReply : Prefix sig.replies 1 :=
  .step .flip left.val 0 right (.stop (some (.flip, right.val)))

private abbrev adversePrim := sig.primitives adverseReply.handler

example : ¬ Shape.denote (withExitUB backedge.native backedge.selected)
      (Syntax.model adversePrim (backedge.bindings left)) 0 ≤
    Shape.denote (withExitUB literalLoop.native literalLoop.selected)
      (Syntax.model adversePrim (literalLoop.bindings left)) 0 := by
  have lower := (backedge.observe_entry backedge.native rfl left adversePrim 0).trans
    ((backedge.observe_step left adversePrim loopStart 0).trans (backedge.observe_step left adversePrim loopNext 1))
  have upper := (literalLoop.observe_entry literalLoop.native rfl left adversePrim 0).trans
    ((literalLoop.observe_step left adversePrim loopStart 0).trans (literalLoop.observe_step left adversePrim loopNext 1))
  change _ = TwoRequest.resultBehaviour (.fault 1) at lower
  change _ = TwoRequest.resultBehaviour .diverge at upper
  rw [lower, upper, TwoRequest.result_order]
  simp [Result.refines]

private def exitPairs : List (Packet Packets × Packet Packets) :=
  [(loopStart, loopStart), (⟨1, left⟩, ⟨1, left⟩),
    (⟨1, right⟩, ⟨1, right⟩), (exitPoint, exitPoint)]

example : source.checkProduct marked left left enumeration exitPairs = true := rfl
example : marked.checkProduct source left left enumeration exitPairs = false := rfl

private def unitCaller : CallerEnumeration (.unit : Syntax.Ty) where
  packets := [unitPayload]
  complete input := by
    obtain ⟨_, typed⟩ := input
    cases typed
    exact List.Mem.head _

private def perLabel : (i : Fin Packets.length) → CallerEnumeration (Packets.get i) :=
  Fin.cases (motive := fun i => CallerEnumeration (Packets.get i)) callers
    (Fin.cases (motive := fun i => CallerEnumeration (Packets.get i.succ)) callers (fun i => by
      obtain rfl := Fin.eq_zero i
      exact unitCaller))

private def inventory : ConfigurationEnumeration Packets where
  configs := (List.finRange Packets.length).flatMap fun i =>
    (perLabel i).packets.map fun input => ⟨i, input⟩
  complete := fun ⟨i, input⟩ =>
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_map.mpr ⟨input, (perLabel i).complete input, rfl⟩⟩

-- The backedges revisit both labels. The result lists each distinct typed
-- pair only once and includes the changed payload.
example : backedge.searchProduct secondLoop left left enumeration inventory inventory =
    .accepted shiftedPairs.reverse := rfl

private def adversePath : List (ProductEdge sig Packets Packets) :=
  [(⟨.flip, ⟨0, right⟩⟩, loopNext, loopNext)]

example : backedge.searchProduct literalLoop left left enumeration inventory inventory =
    .mismatch (loopNext, loopNext) adversePath := rfl

example : ProductPath (backedge.productEdges literalLoop left left enumeration)
      (loopStart, loopStart) adversePath (loopNext, loopNext) ∧
    backedge.productLocal literalLoop left left enumeration (loopNext, loopNext) = false := by
  have checked := backedge.searchProduct_correct literalLoop left left enumeration inventory inventory
  rwa [show backedge.searchProduct literalLoop left left enumeration inventory inventory =
    .mismatch (loopNext, loopNext) adversePath from rfl] at checked

example : ∃ pairs, backedge.checkProduct secondLoop left left enumeration pairs = true :=
  (backedge.searchProduct_accepts_iff secondLoop left left enumeration inventory inventory).mp
    ⟨shiftedPairs.reverse, rfl⟩

example : ¬ ∃ pairs, backedge.checkProduct literalLoop left left enumeration pairs = true := by
  rw [← backedge.searchProduct_accepts_iff literalLoop left left enumeration inventory inventory]
  rintro ⟨_, impossible⟩
  change ProductSearch.Result.mismatch (loopNext, loopNext) adversePath = .accepted _ at impossible
  cases impossible

private abbrev entryQuery : InterpreterScript.Query Op 2 := ⟨.flip, left, 0⟩
private abbrev advanceReply := InterpreterScript.Row.success (S := sig) entryQuery ⟨0, right⟩ 1
private abbrev faultTest : InterpreterScript.Row Op 2 := ⟨⟨.flip, right, 1⟩, .fault 1⟩
private abbrev divergeTest : InterpreterScript.Row Op 2 := ⟨⟨.flip, left, 1⟩, .diverge⟩

private def routeToZero (i : Fin (sig.replies Op.flip).length)
    (a : Syntax.Payload ((sig.replies Op.flip).get i)) : Packet Packets :=
  have typed : Packets.get (0 : Fin 3) = (sig.replies Op.flip).get i := by
    obtain rfl := Fin.eq_zero i
    rfl
  ⟨0, cast (congrArg Syntax.Payload typed.symm) a⟩

private theorem initialSchedule :
    ScheduledPath backedge literalLoop left left (loopStart, loopStart) (0 : Fin 2)
      [] [] (loopStart, loopStart) 0 [] := .start

private theorem adverseSchedule :
    ScheduledPath backedge literalLoop left left (loopStart, loopStart) (0 : Fin 2)
      adversePath [1] (loopNext, loopNext) 1 [advanceReply] :=
  initialSchedule.step (f := Op.flip) (arg := left) (next := routeToZero) (next' := routeToZero)
    rfl rfl ⟨0, right⟩ 1

example : ∃ final rows, ScheduledPath backedge literalLoop left left (loopStart, loopStart) (0 : Fin 2)
    adversePath [1] (loopNext, loopNext) final rows :=
  Table.schedule_rejection (g := backedge) (h := literalLoop) (replies := enumeration)
    (left := inventory) (right := inventory) rfl 0 [1] rfl

private abbrev replayScript := [advanceReply, faultTest, divergeTest]

private theorem adverseConsistent : InterpreterScript.Consistent replayScript :=
  (InterpreterScript.feasible_iff _).mp ⟨adversePrim, by
    intro row mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl <;> rfl⟩

private def rebuilt : Syntax.Primitives Op 2 := InterpreterScript.extend replayScript (fun _ _ _ => .diverge)

example : InterpreterScript.Realizes rebuilt replayScript :=
  InterpreterScript.extend_realizes adverseConsistent _

example : ∃ prim : Syntax.Primitives Op 2,
    ¬ Shape.denote (withExitUB backedge.native backedge.selected)
        (Syntax.model prim (backedge.bindings left)) 0 ≤
      Shape.denote (withExitUB literalLoop.native literalLoop.selected)
        (Syntax.model prim (literalLoop.bindings left)) 0 :=
  ScheduledPath.refutes_queries (raw := backedge.native) (raw' := literalLoop.native)
    rfl rfl adverseSchedule rfl rfl 1 adverseConsistent

private abbrev stayLeft := InterpreterScript.Row.success (S := sig) entryQuery ⟨0, left⟩ 0
private abbrev changeAtSameState := InterpreterScript.Row.success (S := sig) entryQuery ⟨0, right⟩ 0
private def repeatedPath : List (ProductEdge sig Packets Packets) :=
  (⟨.flip, ⟨0, left⟩⟩, loopStart, loopStart) :: adversePath

private theorem repeatedSchedule :
    ScheduledPath backedge literalLoop left left (loopStart, loopStart) (0 : Fin 2)
      repeatedPath [0, 0] (loopNext, loopNext) 0 [stayLeft, changeAtSameState] :=
  (initialSchedule.step (f := Op.flip) (arg := left) (next := routeToZero) (next' := routeToZero)
    rfl rfl ⟨0, left⟩ 0).step (f := Op.flip) (arg := left) (next := routeToZero) (next' := routeToZero)
      rfl rfl ⟨0, right⟩ 0

example : ¬ ∃ prim : Syntax.Primitives Op 2, InterpreterScript.Realizes prim [stayLeft, changeAtSameState] ∧
    backedge.observeAt left prim loopStart 0 = backedge.observeAt left prim loopNext 0 ∧
    literalLoop.observeAt left prim loopStart 0 = literalLoop.observeAt left prim loopNext 0 := by
  intro existsRun
  have consistent := repeatedSchedule.feasible_iff.mp existsRun
  have clash := consistent stayLeft (by simp) changeAtSameState (by simp) rfl
  have payloads := congrArg (fun reply : Syntax.Reply (instrTrg Op.flip) 2 =>
    match reply with
    | .ret payload _ => payload.val
    | _ => .unit) clash
  cases payloads

private abbrev repeatAtStoreOne : InterpreterScript.Query Op 2 := ⟨.flip, left, 1⟩
private abbrev advanceStore := InterpreterScript.Row.success (S := sig) entryQuery ⟨0, left⟩ 1
private abbrev changeAtDifferentState := InterpreterScript.Row.success (S := sig) repeatAtStoreOne ⟨0, right⟩ 1

private def twoStoreInterpreter : Syntax.Primitives Op 2 :=
  InterpreterScript.extend [advanceStore, changeAtDifferentState] (fun _ _ _ => .diverge)

example : InterpreterScript.Realizes twoStoreInterpreter [advanceStore, changeAtDifferentState] := by
  intro row mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> rfl

private def stores (n : Nat) : ScheduleSearch.StateInventory n :=
  ⟨List.finRange n, List.mem_finRange⟩

private theorem adverseWalk : ProductPath (backedge.productEdges literalLoop left left enumeration)
    (loopStart, loopStart) adversePath (loopNext, loopNext) := by
  have checked := backedge.searchProduct_correct literalLoop left left enumeration inventory inventory
  rw [show backedge.searchProduct literalLoop left left enumeration inventory inventory =
    .mismatch (loopNext, loopNext) adversePath from rfl] at checked
  exact checked.1

private theorem repeatedWalk : ProductPath (backedge.productEdges literalLoop left left enumeration)
    (loopStart, loopStart) repeatedPath (loopNext, loopNext) := by
  have first : ProductPath (backedge.productEdges literalLoop left left enumeration)
      (loopStart, loopStart) [(⟨.flip, ⟨0, left⟩⟩, loopStart, loopStart)] (loopStart, loopStart) :=
    .step .start (by decide)
  exact first.step (by decide)

example : backedge.searchSchedule left (loopStart, loopStart) repeatedPath 0 (stores 1) = none := rfl

example : ¬ ∃ schedule final rows,
    ScheduledPath backedge literalLoop left left (loopStart, loopStart) (0 : Fin 1)
      repeatedPath schedule (loopNext, loopNext) final rows ∧ InterpreterScript.Consistent rows := by
  simpa using (Table.searchSchedule_none_iff (initial := 0) (inventory := stores 1)
    (tests := fun _ => []) repeatedWalk).mp rfl

example : (backedge.searchSchedule left (loopStart, loopStart) repeatedPath 0 (stores 2)).map
    ScheduleSearch.Witness.stores = some [1, 0] := rfl

private def withQueryTests (n : Nat) (initial : Fin n) (path : List (ProductEdge sig Packets Packets)) :
    Option (ScheduleSearch.Witness Op n) := do
  let tests ← backedge.queryTests? literalLoop left left (loopNext, loopNext) initial
  backedge.searchSchedule left (loopStart, loopStart) path initial (stores n) tests

-- The prefix fits two states, but its final divergence test conflicts at
-- either state. The third state gives the terminal queries fresh keys.
example : withQueryTests 2 0 repeatedPath = none := rfl
example : (withQueryTests 3 0 repeatedPath).map ScheduleSearch.Witness.stores = some [1, 2] := rfl

private def adverseWitness : ScheduleSearch.Witness Op 2 :=
  ⟨[1], 1, [advanceReply], [⟨⟨.flip, right, 1⟩, .fault 0⟩, divergeTest]⟩

example : withQueryTests 2 0 adversePath = some adverseWitness := rfl

example : (adverseWitness.interpreter Op.flip right 1, adverseWitness.interpreter Op.flip left 1) =
    (.fault 0, .diverge) := rfl

example : ∃ prim : Syntax.Primitives Op 2,
    ¬ Shape.denote (withExitUB backedge.native backedge.selected)
        (Syntax.model prim (backedge.bindings left)) 0 ≤
      Shape.denote (withExitUB literalLoop.native literalLoop.selected)
        (Syntax.model prim (literalLoop.bindings left)) 0 := by
  let tests : Fin 2 → List (InterpreterScript.Row Op 2) :=
    fun final => [⟨⟨.flip, right, final⟩, .fault 0⟩, ⟨⟨.flip, left, final⟩, .diverge⟩]
  obtain ⟨scheduled, terminal, realized⟩ :=
    Table.searchSchedule_sound (initial := 0) (inventory := stores 2) (tests := tests)
      adverseWalk (w := adverseWitness) rfl
  rw [terminal] at realized
  exact scheduled.refutes_queries (raw := backedge.native) (raw' := literalLoop.native)
    rfl rfl rfl rfl 0 ((InterpreterScript.feasible_iff _).mp ⟨_, realized⟩)

example : backedge.runFinite left returnsForever inventory (stores 3) loopStart 0 = .diverge := rfl

example : marked.runFinite left primitives inventory (stores 3) loopStart 0 = .ub := rfl
example : marked.runFinite right primitives inventory (stores 3) loopNext 0 = .fault 2 := rfl
example : source.runFinite left primitives inventory (stores 3) loopStart 0 = .ret 0 2 := rfl

example : source.checkAllInterpreters? marked source.native marked.native left left enumeration
    inventory inventory (stores 1) = some true := rfl

example : marked.checkAllInterpreters? source marked.native source.native left left enumeration
    inventory inventory (stores 1) = some false := rfl

example : source.checkAllInterpreters? marked marked.native marked.native left left enumeration
    inventory inventory (stores 1) = none := rfl

-- These entries have different evaluated arguments. There is no
-- synchronized reply edge to a common downstream mismatch.
example : backedge.productEdges literalLoop right right enumeration (loopNext, loopNext) = [] := rfl

private def unsynchronized : Syntax.Primitives Op 1 := fun _ arg _ =>
  match arg.val with
  | .inr _ => .fault 0
  | _ => .diverge

example : backedge.runFinite right unsynchronized inventory (stores 1) loopNext 0 = .fault 0 := rfl
example : literalLoop.runFinite right unsynchronized inventory (stores 1) loopNext 0 = .diverge := rfl

example : backedge.checkAllInterpreters? literalLoop backedge.native literalLoop.native right right
    enumeration inventory inventory (stores 1) = some false := rfl

example : ¬ Shape.denote (withExitUB backedge.native backedge.selected)
      (Syntax.model unsynchronized (backedge.bindings right)) 0 ≤
    Shape.denote (withExitUB literalLoop.native literalLoop.selected)
      (Syntax.model unsynchronized (literalLoop.bindings right)) 0 := by
  have lower := (backedge.observe_entry backedge.native rfl right unsynchronized 0).trans
    (backedge.observe_runFinite right unsynchronized inventory (stores 1) loopNext 0)
  have upper := (literalLoop.observe_entry literalLoop.native rfl right unsynchronized 0).trans
    (literalLoop.observe_runFinite right unsynchronized inventory (stores 1) loopNext 0)
  intro le
  have compared := Eq.mp (congrArg₂ (· ≤ ·) lower upper) le
  have impossible := (TwoRequest.result_order (.fault (0 : Fin 1)) .diverge).mp compared
  simp [Result.refines] at impossible

private def terminalTable (i : Tag) : Table sig [.unit] where
  entry := 0
  row _ := .exit i
  selected _ := false

example : ∃ prim : Syntax.Primitives Op 2,
    ¬ Shape.denote (withExitUB (terminalTable 0).native (terminalTable 0).selected)
        (Syntax.model prim ((terminalTable 0).bindings unitPayload)) 0 ≤
      Shape.denote (withExitUB (terminalTable 1).native (terminalTable 1).selected)
        (Syntax.model prim ((terminalTable 1).bindings unitPayload)) 0 := by
  have initialPath : ScheduledPath (terminalTable 0) (terminalTable 1) unitPayload unitPayload
      (⟨0, unitPayload⟩, ⟨0, unitPayload⟩) (0 : Fin 2) []
      [] (⟨0, unitPayload⟩, ⟨0, unitPayload⟩) 0 [] := .start
  exact initialPath.refutes_exits (raw := (terminalTable 0).native) (raw' := (terminalTable 1).native)
    rfl rfl (by simp [InterpreterScript.Consistent]) rfl rfl (.inr (by decide))

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduledPath.refutes_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ScheduledPath.refutes_queries

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Table.searchProduct_accepts_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Table.searchProduct_accepts_iff

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Table.checkProduct_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Table.checkProduct_sound

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Table.observe_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Table.observe_entry

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Table.compareInterface_accepts_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Table.compareInterface_accepts_iff

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
