module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Ranked.Thms
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

private def configurationsOf {R : List Syntax.Ty}
    (each : (i : Fin R.length) → CallerEnumeration (R.get i)) : ConfigurationEnumeration R where
  configs := (List.finRange R.length).flatMap fun i =>
    (each i).packets.map fun input => ⟨i, input⟩
  complete := fun ⟨i, input⟩ =>
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
      List.mem_map.mpr ⟨input, (each i).complete input, rfl⟩⟩

private def inventory : ConfigurationEnumeration Packets := configurationsOf perLabel

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

private def sharedCounterexample : EntryCounterexample Op Bit 1 where
  input := right
  initial := 0
  script := [⟨⟨.test, right, 0⟩, .diverge⟩, ⟨⟨.flip, left, 0⟩, .diverge⟩,
    ⟨⟨.flip, right, 0⟩, .fault 0⟩, ⟨⟨.test, left, 0⟩, .diverge⟩]

-- The first shared packet is decoded identically at both ends. Only
-- the later packet reveals that the right decoder always supplies left.
example : readsCaller.compareEntries? readsCaller readsCaller.native readsCaller.native
    callers id (fun _ => left) enumeration inventory inventory (stores 1) =
      some (.counterexample sharedCounterexample) := rfl

example : (sharedCounterexample.interpreter Op.flip right 0, sharedCounterexample.interpreter Op.flip left 0) =
    (.fault 0, .diverge) := rfl

example : ¬ Shape.denote (withExitUB readsCaller.native readsCaller.selected)
      (Syntax.model sharedCounterexample.interpreter (readsCaller.bindings right)) 0 ≤
    Shape.denote (withExitUB readsCaller.native readsCaller.selected)
      (Syntax.model sharedCounterexample.interpreter (readsCaller.bindings left)) 0 :=
  (Table.compareEntries_counterexample (g := readsCaller) (h := readsCaller)
    (raw := readsCaller.native) (raw' := readsCaller.native) (callers := callers)
    (decodeLeft := id) (decodeRight := fun _ => left) (replies := enumeration)
    (left := inventory) (right := inventory) (stores := stores 1) (w := sharedCounterexample) rfl).2.2

private def singletonInventory {A : Syntax.Ty} (domain : CallerEnumeration A) : ConfigurationEnumeration [A] :=
  ⟨domain.packets.map fun v => ⟨0, v⟩, fun ⟨i, v⟩ => by
    obtain rfl := Fin.eq_zero i
    exact List.mem_map.mpr ⟨v, domain.complete v, rfl⟩⟩

private def bitExit : Table sig [Bit] := ⟨0, fun _ => .exit 0, fun _ => false⟩

-- The common bit packet decodes to a bit on the left and unit on the right.
example : bitExit.compareEntries? (terminalTable 0) bitExit.native (terminalTable 0).native
    callers id (fun _ => unitPayload) enumeration (singletonInventory callers)
    (singletonInventory unitCaller) (stores 1) = some .refines := rfl

example : (emptyTable 0).compareEntries? (terminalTable 1) (emptyTable 0).native (terminalTable 1).native
    emptyCallers id (fun _ => unitPayload) enumeration (singletonInventory emptyCallers)
    (singletonInventory unitCaller) (stores 1) = some .refines := rfl

example : (emptyTable 0).compareEntries? (terminalTable 1) (emptyTable 1).native (terminalTable 1).native
    emptyCallers id (fun _ => unitPayload) enumeration (singletonInventory emptyCallers)
    (singletonInventory unitCaller) (stores 1) = none := rfl

private def shiftState (n : Nat) : Fin n ↪ Fin (n + 2) :=
  ⟨fun s => ⟨s.val + 1, by omega⟩, fun a b eq => Fin.ext (by
    have states := congrArg Fin.val eq
    change a.val + 1 = b.val + 1 at states
    omega)⟩

example : ∃ w, readsCaller.compareEntries? readsCaller readsCaller.native readsCaller.native
    callers id (fun _ => left) enumeration inventory inventory (stores 3) = some (.counterexample w) :=
  (Table.compareEntries_rejection_mono (g := readsCaller) (h := readsCaller)
    (raw := readsCaller.native) (raw' := readsCaller.native) (callers := callers)
    (decodeLeft := id) (decodeRight := fun _ => left) (replies := enumeration)
    (left := inventory) (right := inventory) (stores := stores 1) (w := sharedCounterexample)
    (shiftState 1) inventory inventory (stores 3) rfl).2

private def statefulWitness : EntryCounterexample Op Bit 3 where
  input := right
  initial := 0
  script := [
    InterpreterScript.Row.success (S := sig) ⟨.flip, right, 0⟩ ⟨0, left⟩ 1,
    InterpreterScript.Row.success (S := sig) ⟨.test, right, 1⟩ ⟨0, unitPayload⟩ 2,
    ⟨⟨.test, left, 1⟩, .fault 2⟩,
    InterpreterScript.Row.success (S := sig) ⟨.flip, left, 1⟩ ⟨0, left⟩ 1]

private abbrev shiftedWitness := statefulWitness.mapState (shiftState 3)

-- Both queries move to new stores. The two programs take different
-- second requests after the same initial reply.
example : shiftedWitness.input = right ∧ shiftedWitness.initial = 1 := ⟨rfl, rfl⟩

example : readsCaller.runFinite right shiftedWitness.interpreter inventory (stores 5) loopNext 1 =
    .ret 0 3 := rfl

example : source.runFinite right shiftedWitness.interpreter inventory (stores 5) loopNext 1 =
    .fault 3 := rfl

example : (table (.var 1) 1).runFinite right shiftedWitness.interpreter inventory (stores 5) loopNext 1 =
    .ub := rfl

example : backedge.runFinite right shiftedWitness.interpreter inventory (stores 5) loopNext 1 =
    .diverge := rfl

private theorem statefulRefutes :
    ¬ Shape.denote (withExitUB readsCaller.native readsCaller.selected)
        (Syntax.model statefulWitness.interpreter (readsCaller.bindings right)) 0 ≤
      Shape.denote (withExitUB source.native source.selected)
        (Syntax.model statefulWitness.interpreter (source.bindings right)) 0 := by
  have lower := (readsCaller.observe_entry readsCaller.native rfl right statefulWitness.interpreter 0).trans
    (readsCaller.observe_runFinite right statefulWitness.interpreter inventory (stores 3) loopNext 0)
  have upper := (source.observe_entry source.native rfl right statefulWitness.interpreter 0).trans
    (source.observe_runFinite right statefulWitness.interpreter inventory (stores 3) loopNext 0)
  intro le
  have compared := Eq.mp (congrArg₂ (· ≤ ·) lower upper) le
  have impossible := (TwoRequest.result_order (.ret 0 (2 : Fin 3)) (.fault 2)).mp compared
  simp [Result.refines] at impossible

example : ¬ Shape.denote (withExitUB readsCaller.native readsCaller.selected)
      (Syntax.model shiftedWitness.interpreter (readsCaller.bindings right)) 1 ≤
    Shape.denote (withExitUB source.native source.selected)
      (Syntax.model shiftedWitness.interpreter (source.bindings right)) 1 :=
  EntryCounterexample.mapState_refutes (g := readsCaller) (h := source)
    (raw := readsCaller.native) (raw' := source.native) (decodeLeft := id) (decodeRight := id)
    (w := statefulWitness) (shiftState 3) rfl rfl inventory inventory (stores 3) statefulRefutes

private def naturalPrim : Syntax.StatePrimitives Op Nat := fun f arg s =>
  match f with
  | .flip => .ret (pack (L := replies .flip) ⟨0, left⟩) (s + 100)
  | .test =>
    match arg.val with
    | .inr _ => .fault (s + 200)
    | _ => .fault (s + 100)

private def naturalFlip : RunRow Op Nat :=
  ⟨.flip, right, 100, .ret (pack (L := replies .flip) ⟨0, left⟩) 200⟩

private def callerRows : List (RunRow Op Nat) :=
  [naturalFlip, ⟨.test, right, 200, .fault 400⟩]

private def sourceRows : List (RunRow Op Nat) :=
  [naturalFlip, ⟨.test, left, 200, .fault 300⟩]

private theorem callerFinite :
    FiniteRun readsCaller right naturalPrim loopNext 100 callerRows (.fault 400) := by
  refine .repeat (f := Op.flip) (arg := right) (value := pack (L := replies .flip) ⟨0, left⟩) rfl rfl ?_
  exact .fault (f := Op.test) (arg := right) rfl rfl

private theorem sourceFinite :
    FiniteRun source right naturalPrim loopNext 100 sourceRows (.fault 300) := by
  refine .repeat (f := Op.flip) (arg := right) (value := pack (L := replies .flip) ⟨0, left⟩) rfl rfl ?_
  exact .fault (f := Op.test) (arg := left) rfl rfl

private theorem naturalRefutes :
    ¬ Shape.denote (withExitUB readsCaller.native readsCaller.selected)
        (Syntax.model naturalPrim (readsCaller.bindings right)) 100 ≤
      Shape.denote (withExitUB source.native source.selected)
        (Syntax.model naturalPrim (source.bindings right)) 100 := by
  have lower := (readsCaller.observe_entry readsCaller.native rfl right naturalPrim 100).trans callerFinite.observes
  have upper := (source.observe_entry source.native rfl right naturalPrim 100).trans sourceFinite.observes
  intro ordered
  have compared := Eq.mp (congrArg₂ (· ≤ ·) lower upper) ordered
  have bad := (WithTop.coe_le_coe.mp compared) (Set.mem_singleton (Outcome.fault 400))
  have clash : (Outcome.fault 400 : Outcome 2 Unit Nat) = .fault 300 := Set.mem_singleton_iff.mp bad
  cases clash

private abbrev naturalSupport := RunSupport.ofRows 100 (callerRows ++ sourceRows)
private abbrev naturalWitness := naturalSupport.witness right (callerRows ++ sourceRows)

example : naturalSupport.values = [100, 400, 200, 300] := rfl
example : readsCaller.runFinite right naturalWitness.interpreter inventory (stores 4) loopNext naturalWitness.initial =
    .fault (1 : Fin 4) := rfl
example : source.runFinite right naturalWitness.interpreter inventory (stores 4) loopNext naturalWitness.initial =
    .fault (3 : Fin 4) := rfl

example :
    readsCaller.checkAllInterpreters? source readsCaller.native source.native right right
      enumeration inventory inventory (stores 4) = some false ∧
      ∃ w, readsCaller.compareEntries? source readsCaller.native source.native callers id id
        enumeration inventory inventory (stores 4) = some (.counterexample w) :=
  (Table.compress_finite_refutation (g := readsCaller) (h := source)
    (raw := readsCaller.native) (raw' := source.native) (decodeLeft := id) (decodeRight := id)
    (input := right) rfl rfl callerFinite sourceFinite naturalRefutes callers enumeration inventory inventory).2.2.2.2
      (stores 4)

private def quiet : Syntax.StatePrimitives Op Nat := fun _ _ _ => .diverge

example : FiniteRun backedge right quiet loopNext 100 [⟨.flip, right, 100, .diverge⟩] .diverge :=
  .diverge (f := Op.flip) (arg := right) rfl rfl

example : ∃ rows stop, FiniteRun backedge right quiet loopNext 100 rows stop := by
  apply FiniteRun.of_feedback_finite (o := .diverge)
  refine ⟨blockPoint loopNext 100, .refl, ?_⟩
  have localStep : backedge.feedback right quiet (blockPoint loopNext 100) = WithTop.some {Outcome.diverge} :=
    backedge.feedback_step right quiet loopNext 100
  rw [localStep]
  simp [Behaviour.Ordinary, Behaviour.possible, Feedback.external]

example : marked.observeAt right quiet exitPoint 100 = ⊤ :=
  (FiniteRun.exit (g := marked) (caller := right) (prim := quiet) (p := exitPoint) (s := 100)
    (i := 1) (selected := true) rfl).observes

private def ticking : Syntax.StatePrimitives Op Nat := fun f _ s =>
  match f with
  | .flip => .ret (pack (L := replies .flip) ⟨0, right⟩) (s + 1)
  | .test => .diverge

example : Feedback.Infinite (backedge.feedback right ticking) (blockPoint loopNext 0) :=
  ⟨fun n => blockPoint loopNext n, rfl, fun n =>
    (backedge.feedback_step_iff right ticking loopNext n _).mpr ⟨loopNext, n + 1, rfl, rfl⟩⟩

-- The infinite replay above visits state n at step n.
example (support : List Nat) : ∃ n, n ∉ support := by
  suffices ∃ bound, ∀ n, bound ≤ n → n ∉ support by
    obtain ⟨bound, outside⟩ := this
    exact ⟨bound, outside bound le_rfl⟩
  induction support with
  | nil => exact ⟨0, by simp⟩
  | cons a tail ih =>
    obtain ⟨bound, outside⟩ := ih
    refine ⟨max (a + 1) bound, fun n large h => ?_⟩
    have past := (Nat.le_max_left (a + 1) bound).trans large
    have later := (Nat.le_max_right (a + 1) bound).trans large
    rcases List.mem_cons.mp h with rfl | mem
    · omega
    · exact outside n later mem

private def oneRequest (loops : Bool) : Table sig Packets where
  entry := 0
  row := Fin.cases (motive := fun i : Fin 3 => Row sig Packets [Packets.get i, Bit])
    (if loops then backedge.row 0 else source.row 0) (fun _ => .exit 0)
  selected _ := false

private abbrev tickLoop := oneRequest true
private abbrev oneThenExit := oneRequest false
private abbrev tickReply := pack (L := replies .flip) ⟨0, right⟩

private def oneReplyRows (final : Nat) : List (RunRow Op Nat) :=
  [⟨.flip, right, 0, .ret tickReply final⟩]

private theorem tickFinite :
    FiniteRun oneThenExit right ticking loopNext 0 (oneReplyRows 1) (.exit 0 false 1) := by
  refine .repeat (f := Op.flip) (arg := right) (value := tickReply) rfl rfl ?_
  exact .exit rfl

private def tickReplay : GuardedReplay tickLoop right ticking loopNext (0 : Nat) :=
  ⟨fun i => (loopNext, i), rfl, fun _ => rfl⟩

private abbrev tickSupport := RunSupport.ofRows 0 (oneReplyRows 1)
private abbrev tickWitness := tickSupport.witness right (oneReplyRows 1)

example : tickSupport.values = [0, 1] := rfl

-- The first reply is shared. At the same opcode and argument, the next
-- store makes a different key, which the witness answers with divergence.
example : tickReplay.listed (oneReplyRows 1) 0 ∧ ¬ tickReplay.listed (oneReplyRows 1) 1 := by
  refine ⟨⟨_, List.mem_singleton_self _⟩, ?_⟩
  intro recorded
  obtain ⟨_, mem⟩ := recorded
  have different := congrArg RunRow.incoming (List.mem_singleton.mp mem)
  cases different

example : ¬ Feedback.Infinite (tickLoop.feedback right tickWitness.interpreter)
    (blockPoint loopNext tickWitness.initial) :=
  tickReplay.no_infinite_after_cut tickSupport.code tickWitness.interpreter 1
    (fun i smaller => by
      have zero : i = 0 := by omega
      subst i
      rfl) rfl

example : tickLoop.runFinite right tickWitness.interpreter inventory (stores 2) loopNext tickWitness.initial =
    .diverge := rfl

example : oneThenExit.runFinite right tickWitness.interpreter inventory (stores 2) loopNext tickWitness.initial =
    .ret 0 (1 : Fin 2) := rfl

private theorem tickingRefutes :
    ¬ Shape.denote (withExitUB tickLoop.native tickLoop.selected) (Syntax.model ticking (tickLoop.bindings right)) 0 ≤
      Shape.denote (withExitUB oneThenExit.native oneThenExit.selected)
        (Syntax.model ticking (oneThenExit.bindings right)) 0 := by
  have lower := (tickLoop.observe_entry tickLoop.native rfl right ticking 0).trans
    (Table.observe_infinite tickReplay.is_infinite)
  have upper := (oneThenExit.observe_entry oneThenExit.native rfl right ticking 0).trans tickFinite.observes
  intro ordered
  have compared := Eq.mp (congrArg₂ (· ≤ ·) lower upper) ordered
  have impossible := (RunStop.divergence_order (.exit 0 false (1 : Nat))).1.mp compared
  simp at impossible

example : tickLoop.checkAllInterpreters? oneThenExit tickLoop.native oneThenExit.native right right
    enumeration inventory inventory (stores 2) = some false :=
  ((Table.compress_mixed_refutation (g := tickLoop) (h := oneThenExit)
    (raw := tickLoop.native) (raw' := oneThenExit.native) (decodeLeft := id) (decodeRight := id)
    (input := right) rfl rfl (.inl ⟨tickReplay.is_infinite, tickFinite⟩) tickingRefutes
    callers enumeration inventory inventory).2.2.2.2 (stores 2)).1

private def steady : Syntax.StatePrimitives Op Nat := fun f _ s =>
  match f with
  | .flip => .ret tickReply s
  | .test => .diverge

private theorem steadyFinite :
    FiniteRun oneThenExit right steady loopNext 0 (oneReplyRows 0) (.exit 0 false 0) := by
  refine .repeat (f := Op.flip) (arg := right) (value := tickReply) rfl rfl ?_
  exact .exit rfl

private def steadyReplay : GuardedReplay tickLoop right steady loopNext (0 : Nat) :=
  ⟨fun _ => (loopNext, 0), rfl, fun _ => rfl⟩

private abbrev steadySupport := RunSupport.ofRows 0 (oneReplyRows 0)
private abbrev steadyWitness := steadySupport.witness right (oneReplyRows 0)

-- The same table can supply every step. The compressed runner still
-- has an infinite internal replay on its one-state carrier.
example : Feedback.Infinite (tickLoop.feedback right steadyWitness.interpreter)
    (blockPoint loopNext steadyWitness.initial) := by
  have treated := steadyReplay.treatment steadyFinite right
  cases treated with
  | truncate cut _ absent _ _ =>
    exact (absent ⟨_, List.mem_singleton_self _⟩).elim
  | retain _ _ steps =>
    exact steadyReplay.mapped_is_infinite steadySupport.code steadyWitness.interpreter steps

private theorem relabeledFiniteChecks (n : Nat) (states : ScheduleSearch.StateInventory n) :
    backedge.checkEntries? secondLoop backedge.native secondLoop.native callers id id
      enumeration inventory inventory states = some true := by
  refine Table.checkEntries_accepts_iff.mpr ⟨rfl, rfl, fun input prim s => ?_⟩
  have listed : input ∈ [left, right] := callers.complete input
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl
  · exact backedge.checkProduct_sound secondLoop backedge.native secondLoop.native rfl rfl
      left left enumeration shiftedPairs rfl prim s
  · exact backedge.checkProduct_sound secondLoop backedge.native secondLoop.native rfl rfl
      right right enumeration shiftedPairs rfl prim s

universe storeLevel

-- Both admitted CFGs have a request-guarded cycle. The common caller may
-- supply either bit, and the two loops use different internal labels.
example : backedge.DeterministicRefines.{0, storeLevel} secondLoop backedge.native secondLoop.native id id :=
  (Table.finite_model_property (g := backedge) (h := secondLoop)
    (raw := backedge.native) (raw' := secondLoop.native) (callers := callers)
    (decodeLeft := id) (decodeRight := id) (replies := enumeration)
    (left := inventory) (right := inventory) rfl rfl).mpr relabeledFiniteChecks

-- An admitted pair with a counterexample at size two still accepts at
-- size zero, which has no initial state.
example : tickLoop.checkEntries? oneThenExit tickLoop.native oneThenExit.native callers id id
    enumeration inventory inventory (stores 0) = some true := rfl

example : tickLoop.checkEntries? oneThenExit oneThenExit.native oneThenExit.native callers id id
    enumeration inventory inventory (stores 0) = none := rfl

private theorem tickEntriesReject :
    tickLoop.checkEntries? oneThenExit tickLoop.native oneThenExit.native callers id id
      enumeration inventory inventory (stores 2) = some false :=
  Table.checkEntries_rejects_iff.mpr
    (((Table.compress_mixed_refutation (g := tickLoop) (h := oneThenExit)
      (raw := tickLoop.native) (raw' := oneThenExit.native) (decodeLeft := id) (decodeRight := id)
      (input := right) rfl rfl (.inl ⟨tickReplay.is_infinite, tickFinite⟩) tickingRefutes
      callers enumeration inventory inventory).2.2.2.2 (stores 2)).2)

-- A checker witness lifts into an explicitly higher store universe.
example : ∃ (σ : Type 1) (input : Syntax.Payload Bit) (prim : Syntax.StatePrimitives Op σ) (s : σ),
    ¬ Shape.denote (withExitUB tickLoop.native tickLoop.selected)
        (Syntax.model prim (tickLoop.bindings input)) s ≤
      Shape.denote (withExitUB oneThenExit.native oneThenExit.selected)
        (Syntax.model prim (oneThenExit.bindings input)) s :=
  (Table.finite_refutation_iff (g := tickLoop) (h := oneThenExit)
    (raw := tickLoop.native) (raw' := oneThenExit.native) (callers := callers)
    (decodeLeft := id) (decodeRight := id) (replies := enumeration)
    (left := inventory) (right := inventory) rfl rfl).mp ⟨2, stores 2, tickEntriesReject⟩

-- Both peers replay successfully along a backedge under the same
-- interpreter. The left and right loop labels are different.
example : backedge.entryCheck = false ∧ secondLoop.entryCheck = false := ⟨rfl, rfl⟩

private theorem shiftedReplay :
    Feedback.Infinite (secondLoop.feedback left returnsForever) (blockPoint (⟨1, left⟩ : Packet Packets) 0) := by
  let next : Packet Packets := ⟨1, right⟩
  refine ⟨fun j => Nat.casesOn j (blockPoint (⟨1, left⟩ : Packet Packets) 0) (fun _ => blockPoint next 1), rfl, ?_⟩
  intro j
  cases j with
  | zero =>
    exact (secondLoop.feedback_step_iff left returnsForever ⟨1, left⟩ 0 _).mpr ⟨next, 1, rfl, rfl⟩
  | succ j =>
    exact (secondLoop.feedback_step_iff left returnsForever next 1 _).mpr ⟨next, 1, rfl, rfl⟩

example : Shape.denote (withExitUB backedge.native backedge.selected)
      (Syntax.model returnsForever (backedge.bindings left)) 0 =
    Shape.denote (withExitUB secondLoop.native secondLoop.selected)
      (Syntax.model returnsForever (secondLoop.bindings left)) 0 :=
  Table.both_infinite_observations rfl rfl infiniteReplay shiftedReplay

example : backedge.reachableCutoff secondLoop callers id id enumeration inventory inventory = 2 := rfl

private theorem reachableRelabeled :
    backedge.checkReachableEntries? secondLoop backedge.native secondLoop.native callers id id
      enumeration inventory inventory = some true :=
  relabeledFiniteChecks _ _

example : backedge.DeterministicRefines.{0, storeLevel} secondLoop backedge.native secondLoop.native id id :=
  (Table.checkReachableEntries_accepts_iff rfl rfl).mp reachableRelabeled

-- Both paths below reach the same mismatch. The longer path first takes
-- an avoidable self-edge with a left reply. The right reply changes the packet.
private abbrev repeatedEdge : ProductEdge sig Packets Packets :=
  (⟨.flip, ⟨0, left⟩⟩, loopStart, loopStart)

example : ProductPath (backedge.productEdges literalLoop left left enumeration)
    (loopStart, loopStart) (repeatedEdge :: adversePath) (loopNext, loopNext) :=
  .step (.step .start (by decide)) (by decide)

example : (ProductPath.vertices (loopStart, loopStart) adversePath).Nodup := by decide

example {path : List (ProductEdge sig Packets Packets)}
    (walk : ProductPath (backedge.productEdges literalLoop left left enumeration)
      (loopStart, loopStart) path (loopNext, loopNext)) :
    adversePath.length ≤ path.length := by
  cases path with
  | nil => cases congrArg (fun p => p.1.2.val) walk.nil_end
  | cons => simp [adversePath]

example : ∃ prim : Syntax.Primitives Op 2,
    ¬ Shape.denote (withExitUB backedge.native backedge.selected) (Syntax.model prim (backedge.bindings left)) 0 ≤
      Shape.denote (withExitUB literalLoop.native literalLoop.selected) (Syntax.model prim (literalLoop.bindings left)) 0 :=
  Table.product_path_refutes (left := inventory) (right := inventory) rfl rfl adverseWalk rfl

private def decodeLoopCaller (_ : Syntax.Payload (.unit : Syntax.Ty)) := left

example : literalLoop.entryCheck = false := rfl

example : backedge.reachableCutoff literalLoop unitCaller decodeLoopCaller decodeLoopCaller
    enumeration inventory inventory = 2 := rfl

example : backedge.checkReachableEntries? literalLoop backedge.native literalLoop.native
    unitCaller decodeLoopCaller decodeLoopCaller enumeration inventory inventory = some false := by
  obtain ⟨prim, refutes⟩ := Table.product_path_refutes (raw := backedge.native) (raw' := literalLoop.native)
    (left := inventory) (right := inventory) rfl rfl adverseWalk rfl
  exact Table.checkReachableEntries_rejects_of_refutation rfl rfl unitCaller enumeration inventory inventory
    unitPayload prim 0 refutes

example : backedge.checkReachableEntries? secondLoop silentCycle secondLoop.native callers id id
    enumeration inventory inventory = none := rfl

private def constantRequest {R Γ : List Syntax.Ty} (target : Fin R.length) (typed : R.get target = Bit) :
    Row sig R Γ :=
  .request .flip (.inl .unit) (fun _ => target) fun i => by
    obtain rfl := Fin.eq_zero i
    exact typed

private abbrev ShortPackets : List Syntax.Ty := [Bit, Bit]
private abbrev LongPackets : List Syntax.Ty := [.unit, Bit, Bit]

private def shortCall : Table sig ShortPackets where
  entry := 1
  row := Fin.cases (motive := fun i => Row sig ShortPackets [ShortPackets.get i, Bit])
    (.exit 0) (fun _ => constantRequest 0 rfl)
  selected _ := false

private def longCall : Table sig LongPackets where
  entry := 0
  row := Fin.cases (motive := fun i => Row sig LongPackets [LongPackets.get i, .unit])
    (constantRequest 1 rfl)
    (Fin.cases (motive := fun i => Row sig LongPackets [LongPackets.get i.succ, .unit])
      (constantRequest 2 rfl) (fun _ => .exit 0))
  selected _ := false

private def shortCallers : (i : Fin ShortPackets.length) → CallerEnumeration (ShortPackets.get i) :=
  Fin.cases (motive := fun i => CallerEnumeration (ShortPackets.get i)) callers (fun i => by
    obtain rfl := Fin.eq_zero i
    exact callers)

private def shortInventory : ConfigurationEnumeration ShortPackets := configurationsOf shortCallers

private def longInventory : ConfigurationEnumeration LongPackets :=
  configurationsOf (Fin.cases (motive := fun i => CallerEnumeration (LongPackets.get i)) unitCaller shortCallers)

-- The entries have different labels and types. The shared unit packet
-- independently decodes to a bit on the left and unit on the right.
example : shortCall.rankedCutoff longCall = 2 := rfl

example : shortCall.checkEntries? longCall shortCall.native longCall.native unitCaller (fun _ => left) id
    enumeration shortInventory longInventory (stores 1) = some true := rfl

example : shortCall.checkRankedEntries? longCall shortCall.native longCall.native unitCaller (fun _ => left) id
    enumeration shortInventory longInventory = some false := rfl

private def cutoffPrimitives : Syntax.Primitives Op 2 := fun f _ s =>
  match f with
  | .flip => if s = 0 then .ret (pack (L := replies .flip) ⟨0, left⟩) 1 else .fault 1
  | .test => .diverge

-- One request returns, while the second call to the same instruction
-- and argument sees the updated store and faults.
example : ¬ Shape.denote (withExitUB shortCall.native shortCall.selected)
      (Syntax.model cutoffPrimitives (shortCall.bindings left)) 0 ≤
    Shape.denote (withExitUB longCall.native longCall.selected)
      (Syntax.model cutoffPrimitives (longCall.bindings unitPayload)) 0 := by
  have lower := (shortCall.observe_entry shortCall.native rfl left cutoffPrimitives 0).trans
    (shortCall.observe_runFinite left cutoffPrimitives shortInventory (stores 2) ⟨1, left⟩ 0)
  have upper := (longCall.observe_entry longCall.native rfl unitPayload cutoffPrimitives 0).trans
    (longCall.observe_runFinite unitPayload cutoffPrimitives longInventory (stores 2) ⟨0, unitPayload⟩ 0)
  intro ordered
  have compared := Eq.mp (congrArg₂ (· ≤ ·) lower upper) ordered
  have impossible := (TwoRequest.result_order (.ret 0 (1 : Fin 2)) (.fault 1)).mp compared
  simp [Result.refines] at impossible

private abbrev oneThenUB : Table sig Packets := { oneThenExit with selected := fun _ => true }

-- The shared request can leave the ranked endpoint at an exit and the
-- other endpoint replaying indefinitely. Its ordinary divergence is below
-- the selected target exit, while the opposite direction fails.
example : tickLoop.entryCheck = false := rfl
example : oneThenUB.entryCheck = true := rfl
example : tickLoop.rankedCutoff oneThenUB = 2 := rfl
example : oneThenUB.rankedCutoff tickLoop = 2 := rfl

private theorem cyclicToUB : tickLoop.checkRankedEntries? oneThenUB tickLoop.native oneThenUB.native
    callers id id enumeration inventory inventory = some true := by
  change tickLoop.checkEntries? oneThenUB tickLoop.native oneThenUB.native
    callers id id enumeration inventory inventory (stores 2) = some true
  refine Table.checkEntries_accepts_iff.mpr ⟨rfl, rfl, fun input prim s => ?_⟩
  let pairs (a : Syntax.Payload Bit) : List (Packet Packets × Packet Packets) :=
    [(⟨0, a⟩, ⟨0, a⟩), (⟨0, left⟩, ⟨1, left⟩), (⟨0, right⟩, ⟨1, right⟩)]
  have listed : input ∈ [left, right] := callers.complete input
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl
  · exact tickLoop.checkProduct_sound oneThenUB tickLoop.native oneThenUB.native rfl rfl
      left left enumeration (pairs left) rfl prim s
  · exact tickLoop.checkProduct_sound oneThenUB tickLoop.native oneThenUB.native rfl rfl
      right right enumeration (pairs right) rfl prim s

example : tickLoop.DeterministicRefines.{0, storeLevel} oneThenUB tickLoop.native oneThenUB.native id id :=
  (Table.checkRankedEntries_accepts_iff rfl rfl (Or.inr rfl)).mp cyclicToUB

private theorem tickingReversesUB :
    ¬ Shape.denote (withExitUB oneThenUB.native oneThenUB.selected)
        (Syntax.model ticking (oneThenUB.bindings right)) 0 ≤
      Shape.denote (withExitUB tickLoop.native tickLoop.selected)
        (Syntax.model ticking (tickLoop.bindings right)) 0 := by
  have finite : FiniteRun oneThenUB right ticking loopNext 0 (oneReplyRows 1) (.exit 0 true 1) := by
    refine .repeat (f := Op.flip) (arg := right) (value := tickReply) rfl rfl (.exit rfl)
  have lower := (oneThenUB.observe_entry oneThenUB.native rfl right ticking 0).trans finite.observes
  have upper := (tickLoop.observe_entry tickLoop.native rfl right ticking 0).trans
    (Table.observe_infinite tickReplay.is_infinite)
  intro ordered
  have compared := Eq.mp (congrArg₂ (· ≤ ·) lower upper) ordered
  simp [RunStop.behaviour] at compared

example : oneThenUB.checkRankedEntries? tickLoop oneThenUB.native tickLoop.native
    callers id id enumeration inventory inventory = some false :=
  Table.checkRankedEntries_rejects_of_refutation rfl rfl (Or.inl rfl)
    callers enumeration inventory inventory right ticking 0 tickingReversesUB

example : tickLoop.checkRankedEntries? oneThenExit tickLoop.native oneThenExit.native
    callers id id enumeration inventory inventory = some false := rfl

example : oneThenExit.checkRankedEntries? tickLoop oneThenExit.native tickLoop.native
    callers id id enumeration inventory inventory = some false := rfl

example : tickLoop.checkRankedEntries? tickLoop tickLoop.native tickLoop.native callers id id
    enumeration inventory inventory = none := rfl

example : oneThenExit.checkRankedEntries? oneThenExit source.native oneThenExit.native callers id id
    enumeration inventory inventory = none := rfl

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
