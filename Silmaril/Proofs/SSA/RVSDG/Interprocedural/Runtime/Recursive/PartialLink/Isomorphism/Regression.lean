module

import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Infer.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Executable.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms
meta import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Defs

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Tests

open Continuation.Partial (Config Eval Primitives Site)
open Continuation.Partial.Executable (Actions runFor)
open Continuation.Descent (Pending)

private abbrev T := Ty Unit Unit
private abbrev num : T := .value (.data ())
private abbrev global : T := .value (.global (.data ()))
private abbrev args : Ports T := [num]
private abbrev exports : Ports T := [global, global]

private inductive Op : Dialect (ValueSort Unit Unit) Unit where
  | seed : Op [num] [num]
  | gain : Op [num] [num]
  | finish : Op [global, num] [num]

private def machine : Machine Op where
  Data _ := Nat
  State _ := Unit
  primitive
    | .seed, .cons (.data n) .nil => .cons (.data (n + 7)) .nil
    | .gain, .cons (.data n) .nil => .cons (.data (n + 14)) .nil
    | .finish, .cons (.global _ _ (.data n)) (.cons (.data _) .nil) => .cons (.data (n + 1)) .nil

private def number (n : Nat) : Tuple machine.Val [num] := .cons (.data n) .nil

private def actions : Actions machine Nat where
  step
    | .seed, .cons (.data n) .nil => fun store => some (number ((show Nat from n) + 7), store + 3)
    | .gain, .cons (.data n) .nil => fun store => some (number ((show Nat from n) + 14), store + 6)
    | .finish, .cons (.global _ _ (.data n)) (.cons (.data flag) .nil) => fun store =>
      let test : Nat := flag
      if test = 0 then none else some (number ((show Nat from n) + 1), store + 5)

private def primitives : Primitives machine Nat := actions.toPrimitives

private def positions : Fin 3 ≃ Fin 3 :=
  (Equiv.swap 0 1).trans (Equiv.swap 0 2)

private def ids : GlobalRel := fun left right =>
  left.1 = right.1 ∧ renameVertex positions left.2 = right.2

private theorem respectsGlobals (ids : GlobalRel) : ActionsRespect primitives ids := by
  intro ins outs opcode left right paired store
  cases opcode with
  | seed =>
    cases paired with
    | cons head tail =>
      cases head with
      | data n =>
        cases tail
        exact .returned (.cons (.data _) .nil) (store + 3)
  | gain =>
    cases paired with
    | cons head tail =>
      cases head with
      | data n =>
        cases tail
        exact .returned (.cons (.data _) .nil) (store + 6)
  | finish =>
    cases paired with
    | cons captured rest =>
      cases captured with
      | global _ payload =>
        cases payload with
        | data n =>
          cases rest with
          | cons head tail =>
            cases head with
            | data flag =>
              cases tail
              let test : Nat := flag
              change ActionRelated machine ids Nat [num]
                (_root_.Part.ofOption (if test = 0 then none else some (number ((show Nat from n) + 1), store + 5)))
                (_root_.Part.ofOption (if test = 0 then none else some (number ((show Nat from n) + 1), store + 5)))
              split
              · exact .undefined
              · exact .returned (.cons (.data _) .nil) (store + 5)

private theorem respects : ActionsRespect primitives ids := respectsGlobals ids

private def seedTerm : Term Op [num] [] [[num]] [num] :=
  .bind ⟨[num], .simple .seed, .cons (.arg .head) .nil, fun i => i.elim0⟩
    (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def finishTail : Term Op [global, num] [[num]] [] [num] :=
  .ret (.cons (.output (0 : Fin 1) .head) .nil)

private def finishTerm : Term Op [global, num] [] [[num]] [num] :=
  .bind ⟨[global, num], .simple .finish, .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
      fun i => i.elim0⟩ (fun i => i.elim0) finishTail

private def seedDelta (past : List (Ports T)) : DeltaTerm Op args past (.data ()) :=
  ⟨[num], .cons (.arg .head) .nil, [[num]], seedTerm⟩

private def finishL : DeltaTerm Op args [[global]] (.data ()) :=
  ⟨[global, num], .cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil), [[num]], finishTerm⟩

private def finishR : DeltaTerm Op args [[], [global]] (.data ()) :=
  ⟨[global, num], .cons (.output (1 : Fin 2) .head) (.cons (.arg .head) .nil), [[num]], finishTerm⟩

private def leftTerm : OmegaTerm Op args exports [[global], [global], []] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.delta finishL) <| .bind (.phi (emptyPhi Op args _)) <|
    .ret (.cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))⟩

private def rightTerm : OmegaTerm Op args exports [[], [global], [global]] :=
  ⟨.bind (.phi (emptyPhi Op args [])) <| .bind (.delta (seedDelta [[]])) <| .bind (.delta finishR) <|
    .ret (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil))⟩

private theorem fixedAddresses {n : Nat} (addresses : List Address) :
    addresses.map (Address.rename (renameVertex (Equiv.refl (Fin n)))) = addresses := by
  have fixed (address : Address) : address.rename (renameVertex (Equiv.refl (Fin n))) = address := by
    cases address with
    | arg => rfl
    | output i port =>
      change Address.output (renameVertex (Equiv.refl (Fin n)) i) port = .output i port
      unfold renameVertex
      split <;> rfl
  induction addresses with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, fixed, ih]

private theorem noChildren_refl {ins outs : Ports T} {sigs : List (Ports T)}
    (graph : Graph Op ins [] sigs outs) (empty : ∀ i, (graph.nodes i).shape.regionCount = 0) :
    Graph.Isomorphic Op graph graph := by
  refine .intro rfl rfl (Equiv.refl _) (fun _ => rfl) (fun _ => fixedAddresses _) (fixedAddresses _) ?_
  intro i arm
  exact (Fin.cast (empty i) arm).elim0

private theorem iso : leftTerm.toGraph.RenumberedBy rightTerm.toGraph positions := by
  refine ⟨?_, rfl⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .delta ⟨⟨rfl, rfl⟩, noChildren_refl _ (fun i => Fin.cases rfl (fun j => j.elim0) i)⟩
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact .delta ⟨⟨rfl, rfl⟩, noChildren_refl _ (fun i => Fin.cases rfl (fun j => j.elim0) i)⟩
    · refine Fin.cases ?_ (fun l => l.elim0) k
      exact .phi ⟨⟨rfl, rfl⟩, fun i => i.elim0⟩

private theorem ordered : Ordered Op (renameVertex positions) args exports
    leftTerm.toGraph.toTerm.region rightTerm.toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .emptyRight (.bind rfl (.delta ⟨rfl, rfl⟩ seedTerm)
    (.bind rfl (.delta ⟨rfl, rfl⟩ finishTerm) (.emptyLeft (.ret _ _))))

private theorem paired (flag : Nat) :
    OutcomesRelated machine ids Nat (renameVertex positions) exports
      (link primitives 73 leftTerm.toGraph (number flag) 20)
      (link primitives 73 rightTerm.toGraph (number flag) 20) :=
  link_related respects iso ordered (fun _ => ⟨rfl, rfl⟩) (.cons (.data flag) .nil) 20

private def globalValue (vertex n : Nat) : machine.Val global := .global 73 vertex (.data n)

private theorem matchingGlobal (vertex value : Nat) {other : machine.Val global}
    (paired : ValueRelated machine ids (globalValue vertex value) other) :
    other = globalValue (renameVertex positions vertex) value := by
  change ValueRelated machine ids (.global 73 vertex (.data value)) other at paired
  cases paired with
  | global identity payload =>
    cases payload with
    | data =>
      obtain ⟨unit, address⟩ := identity
      cases unit
      cases address
      rfl

private def finishInputs (vertex payload flag : Nat) : Tuple machine.Val [global, num] :=
  .cons (globalValue vertex payload) (number flag)

private def finishSite (vertex payload flag : Nat) : Site machine :=
  ⟨[global, num], [num], .finish, fun i => i.elim0, fun i => embed (i.elim0), finishInputs vertex payload flag⟩

private theorem matchingSite {other : Site machine}
    (paired : SitesRelated machine ids (finishSite 0 7 0) other) :
    other = finishSite 1 7 0 := by
  cases paired with
  | same inputs =>
    change TupleRelated machine ids (.cons (globalValue 0 7) (number 0)) _ at inputs
    cases inputs with
    | cons global flag =>
      have address := matchingGlobal 0 7 global
      cases address
      cases flag with
      | cons value tail =>
        cases value
        cases tail
        rfl

private def seedSite (flag : Nat) : Site machine :=
  ⟨[num], [num], .seed, fun i => i.elim0, fun i => embed (i.elim0), number flag⟩

private theorem seedRuns (flag : Nat) :
    Eval primitives (.region (embed seedTerm) (number flag) PUnit.unit) 20 (.returned (number (flag + 7)) 23) := by
  refine Eval.bind (value := number (flag + 7)) (middle := 23) ?_ ?_
  · refine Eval.primitive (seedSite flag) ?_
    exact _root_.Part.mem_some _
  · exact .ret _ _ _ _

private def blockedFrame (vertex : Nat) : Pending machine [num] [num] :=
  .bind (past := []) (embed finishTail) (finishInputs vertex 7 0) PUnit.unit .empty

private theorem finishBlocks (vertex : Nat) :
    Eval primitives (.region (embed finishTerm) (finishInputs vertex 7 0) PUnit.unit) 23
      (.blocked (finishSite vertex 7 0) (blockedFrame vertex) 23) :=
  .bindBlocked (.primitiveBlocked (finishSite vertex 7 0) 23 rfl)

private theorem finishReturns (vertex : Nat) :
    Eval primitives (.region (embed finishTerm) (finishInputs vertex 8 1) PUnit.unit) 23
      (.returned (number 9) 28) := by
  refine Eval.bind (value := number 9) (middle := 28) ?_ ?_
  · refine Eval.primitive (finishSite vertex 8 1) ?_
    exact _root_.Part.mem_some _
  · exact .ret _ _ _ _

private theorem openInitializer {context : Ports T} {sigs : List (Ports T)}
    (term : Term Op context [] sigs [num]) (inputs : Tuple machine.Val context) :
    Job.region (m := machine) (past := []) (embed term.toGraph.toTerm) inputs PUnit.unit =
      .region (embed term) inputs PUnit.unit :=
  congrArg (fun code => Job.region (m := machine) (past := []) (embed code) inputs PUnit.unit)
    (Term.toTerm_toGraph term)

private def failure (δ source : Nat) : Failure machine Nat := ⟨73, δ, finishSite source 7 0, 23⟩

private def readyExports (first second : Nat) : Tuple machine.Val exports :=
  .cons (globalValue first 8) (.cons (globalValue second 9) .nil)

private theorem blockedL : Links primitives 73 leftTerm.toGraph (number 0) 20 (.undefined (failure 1 0)) := by
  refine LinksTable.bind (values := (.cons (globalValue 0 7) .nil : Tuple machine.Val [global]))
    (middle := 23) ?_ (.stop ?_)
  · refine LinksDelta.linked (initialized := number 7) ?_
    change Eval primitives (.region (embed seedTerm.toGraph.toTerm) (number 0) PUnit.unit) _ _
    rw [openInitializer seedTerm (number 0)]
    exact seedRuns 0
  · refine LinksDelta.undefined (pending := blockedFrame 0) ?_
    change Eval primitives (.region (embed finishTerm.toGraph.toTerm) (finishInputs 0 7 0) PUnit.unit) _ _
    rw [openInitializer finishTerm (finishInputs 0 7 0)]
    exact finishBlocks 0

example : link primitives 73 leftTerm.toGraph (number 0) 20 = .undefined (failure 1 0) :=
  outcome_unique link_spec blockedL

-- The first δ ran before the later action blocked. Its allocation and
-- the later δ both moved. The blocked operand still contains the related global.
example : ∃ right, link primitives 73 rightTerm.toGraph (number 0) 20 = .undefined right ∧
    right.vertex = 2 ∧ right.store = 23 ∧ right.site = finishSite 1 7 0 := by
  have related := paired 0
  rw [outcome_unique link_spec blockedL] at related
  generalize link primitives 73 rightTerm.toGraph (number 0) 20 = observed at related ⊢
  cases related with
  | undefined position _ sites store =>
    exact ⟨_, rfl, position.symm, rfl, matchingSite sites⟩

private theorem successL : Links primitives 73 leftTerm.toGraph (number 1) 20 (.linked (readyExports 0 1) 28) := by
  refine LinksTable.bind (values := (.cons (globalValue 0 8) .nil : Tuple machine.Val [global]))
    (middle := 23) ?_ ?_
  · refine LinksDelta.linked (initialized := number 8) ?_
    change Eval primitives (.region (embed seedTerm.toGraph.toTerm) (number 1) PUnit.unit) _ _
    rw [openInitializer seedTerm (number 1)]
    exact seedRuns 1
  · refine LinksTable.bind (values := (.cons (globalValue 1 9) .nil : Tuple machine.Val [global]))
      (middle := 28) ?_ (.bind (values := (.nil : Tuple machine.Val [])) (middle := 28) rfl (.ret _ _ _ _))
    refine LinksDelta.linked (initialized := number 9) ?_
    change Eval primitives (.region (embed finishTerm.toGraph.toTerm) (finishInputs 0 8 1) PUnit.unit) _ _
    rw [openInitializer finishTerm (finishInputs 0 8 1)]
    exact finishReturns 0

example : ∃ right, link primitives 73 rightTerm.toGraph (number 1) 20 = .linked right 28 ∧
    right.get .head = globalValue 1 8 ∧ right.get (.tail .head) = globalValue 2 9 := by
  have related := paired 1
  rw [outcome_unique link_spec successL] at related
  generalize link primitives 73 rightTerm.toGraph (number 1) 20 = observed at related ⊢
  cases related with
  | linked exports =>
    exact ⟨_, rfl, matchingGlobal 0 8 (exports.get .head), matchingGlobal 1 9 (exports.get (.tail .head))⟩

private abbrev fn : Function Unit Unit := ⟨[num, .control 2], [num]⟩
private abbrev bodyInput : Ports T := [global, fn.port, num, .control 2]

private abbrev effect {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyInput past [num] :=
  ⟨[global, num], .base (.simple (.primitive .finish)),
    .cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil), fun i => i.elim0⟩

private abbrev emptyBranch {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyInput past [] :=
  ⟨[.control 2], .base (.gamma (entry := []) (exit := []) 0),
    .cons (.arg (.tail (.tail (.tail .head)))) .nil, fun _ => []⟩

private abbrev callSelf {past : List (Ports T)} : NestedTheta.Node (Instruction Op) bodyInput past [num] :=
  ⟨fn.port :: fn.args, .base (.simple (.apply fn)),
    .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head)))
      (.cons (.arg (.tail (.tail (.tail .head)))) .nil)), fun i => i.elim0⟩

-- The caller retains the finish result across the recursive application.
-- The independent empty γ moves, but the effect still precedes the call.
private def memberBodyL : NestedTheta.Term (Instruction Op) bodyInput [] [[num], [], [num]] [num] :=
  .bind effect (fun i => i.elim0) <| .bind emptyBranch (fun _ => .ret .nil) <|
    .bind callSelf (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 3) .head) .nil))

private def memberBodyR : NestedTheta.Term (Instruction Op) bodyInput [] [[], [num], [num]] [num] :=
  .bind emptyBranch (fun _ => .ret .nil) <| .bind effect (fun i => i.elim0) <|
    .bind callSelf (fun i => i.elim0) (.ret (.cons (.output (1 : Fin 3) .head) .nil))

private def bodyPositions : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

private theorem memberBodyIso :
    NestedTheta.Graph.Isomorphic (Instruction Op) memberBodyL.toGraph memberBodyR.toGraph := by
  refine .intro rfl rfl bodyPositions ?_ ?_ rfl ?_
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => i.elim0)))
  · refine Fin.cases (fun j => j.elim0) (Fin.cases ?_ (Fin.cases (fun j => j.elim0) (fun i => i.elim0)))
    intro arm
    exact .intro rfl rfl (Equiv.refl _) (fun i => i.elim0) (fun i => i.elim0) rfl (fun i => i.elim0)

private def selfGroup (member : Function Unit Unit) {past sigs : List (Ports T)} {capture : T}
    (source : Origin args past capture)
    (body : NestedTheta.Term (Instruction Op) ([capture, member.port] ++ member.args) [] sigs member.results) :
    PhiTerm Op args past [member] :=
  ⟨[capture], .cons source .nil,
    .cons ⟨[capture, member.port], .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), sigs, body⟩ .nil⟩

private def groupL := selfGroup fn (.output (0 : Fin 1) .head : Origin args [[global]] global) memberBodyL
private def groupR := selfGroup fn (.output (1 : Fin 2) .head : Origin args [[], [global]] global) memberBodyR

private def recursiveL : OmegaTerm Op args [fn.port] [[global], [fn.port], []] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.phi groupL) <| .bind (.phi (emptyPhi Op args _)) <|
    .ret (.cons (.output (1 : Fin 3) .head) .nil)⟩

private def recursiveR : OmegaTerm Op args [fn.port] [[], [global], [fn.port]] :=
  ⟨.bind (.phi (emptyPhi Op args [])) <| .bind (.delta (seedDelta [[]])) <| .bind (.phi groupR) <|
    .ret (.cons (.output (2 : Fin 3) .head) .nil)⟩

private theorem groupsIso : groupL.Renumbered (renameVertex positions) groupR :=
  ⟨⟨rfl, rfl⟩, Fin.cases ⟨⟨rfl, rfl⟩, memberBodyIso⟩ (fun i => i.elim0)⟩

private theorem recursiveIso : recursiveL.toGraph.RenumberedBy recursiveR.toGraph positions :=
  (recursiveL.renumberedBy_toGraph_iff recursiveR positions).2
    ⟨Fin.cases (.delta ⟨⟨rfl, rfl⟩, noChildren_refl _ (fun i => Fin.cases rfl (fun j => j.elim0) i)⟩)
      (Fin.cases (.phi groupsIso) (Fin.cases (.phi ⟨⟨rfl, rfl⟩, fun i => i.elim0⟩) (fun i => i.elim0))), rfl⟩

private theorem recursiveOrder : Ordered Op (renameVertex positions) args [fn.port]
    recursiveL.toGraph.toTerm.region recursiveR.toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .emptyRight (.bind rfl (.delta ⟨rfl, rfl⟩ seedTerm)
    (.bind rfl (.phi groupsIso) (.emptyLeft (.ret _ _))))

private def refL : machine.Val fn.port :=
  .member (.cons (globalValue 0 8) .nil) groupL.toGraph.definitions 0

private def refR : machine.Val fn.port :=
  .member (.cons (globalValue 1 8) .nil) groupR.toGraph.definitions 0

private theorem recursiveLinksL :
    link primitives 73 recursiveL.toGraph (number 1) 20 = .linked (.cons refL .nil) 23 :=
  (Executable.link_eq actions 73 recursiveL.toGraph (number 1) 20).symm.trans (by cbv)

private theorem recursiveLinksR :
    link primitives 73 recursiveR.toGraph (number 1) 20 = .linked (.cons refR .nil) 23 :=
  (Executable.link_eq actions 73 recursiveR.toGraph (number 1) 20).symm.trans (by cbv)

-- Slot zero sees its own linked reference and the relocated δ in capture order.
example : resolve machine refL =
    ⟨[global, fn.port], .cons (globalValue 0 8) (.cons refL .nil), _, memberBodyL.toGraph⟩ := rfl

example : resolve machine refR =
    ⟨[global, fn.port], .cons (globalValue 1 8) (.cons refR .nil), _, memberBodyR.toGraph⟩ := rfl

private theorem recursiveCallees : ValueRelated machine ids refL refR := by
  have imports : TupleRelated machine ids (number 1) (number 1) :=
    .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) (1 : Nat)) .nil
  have paired := link_related (unitL := 73) (unitR := 73) respects recursiveIso recursiveOrder
    (fun _ => ⟨rfl, rfl⟩) imports 20
  rw [recursiveLinksL, recursiveLinksR] at paired
  cases paired with
  | linked exports => exact exports.get .head

example : TupleRelated machine ids (resolve machine refL).values (resolve machine refR).values ∧
    NestedTheta.Graph.Isomorphic (Instruction Op) (resolve machine refL).body (resolve machine refR).body :=
  resolve_related recursiveCallees

private def recursiveArgs : Tuple machine.Val fn.args := .cons (.data (1 : Nat)) (.cons (.control 0) .nil)

private def recursivePrefix {sigs : List (Ports T)} (graph : Omega Op args [fn.port] sigs) :
    Option (Config machine Nat [num]) :=
  (Executable.start actions 73 graph (number 1) .head recursiveArgs 20).toOption.map (runFor actions 20)

open RecursiveCall (Schedule ResolvedSchedule Frames Live Advance DispatchReady)
open Continuation (Stack)

private def memberVertices : Nat ≃ Nat := Equiv.swap 0 1

private theorem memberSchedule :
    Schedule Op memberVertices memberBodyL memberBodyR :=
  .emptyRight _ (.bind (.primitive Op.finish) _ _ rfl rfl
    (.emptyLeft _ (.bind (.apply fn) _ _ rfl rfl (.ret _ _ rfl))))

private theorem selectedSchedule : ResolvedSchedule Op machine fn (resolve machine refL) (resolve machine refR) := by
  apply ResolvedSchedule.intro (vertices := memberVertices)
  change Schedule Op memberVertices memberBodyL.toGraph.toTerm memberBodyR.toGraph.toTerm
  simpa only [NestedTheta.Term.toTerm_toGraph] using memberSchedule

private theorem relatedArgs : TupleRelated machine ids recursiveArgs recursiveArgs :=
  .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) (1 : Nat)) (.cons (.control 0) .nil)

private def entryOf (vertex : Nat) (ref : machine.Val fn.port) : Tuple machine.Val bodyInput :=
  .cons (globalValue vertex 8) (.cons ref recursiveArgs)

private def storedL : Locals machine.Val [[num], []] := (number 9, .nil, PUnit.unit)
private def storedR : Locals machine.Val [[], [num]] := (.nil, number 9, PUnit.unit)

private def savedL (outer : Stack machine [num] [num]) : Stack machine [num] [num] :=
  .resume (past := [[num], []]) (.ret (.cons (.output (0 : Fin 3) .head) .nil)) (entryOf 0 refL) storedL outer

private def savedR (outer : Stack machine [num] [num]) : Stack machine [num] [num] :=
  .resume (past := [[], [num]]) (.ret (.cons (.output (1 : Fin 3) .head) .nil)) (entryOf 1 refR) storedR outer

private theorem savedPair {left right : Stack machine [num] [num]} (outer : Frames machine ids [num] left right) :
    Frames machine ids [num] (savedL left) (savedR right) := by
  have entry : TupleRelated machine ids (entryOf 0 refL) (entryOf 1 refR) :=
    .cons (.global ⟨rfl, rfl⟩ (ValueRelated.data (m := machine) (ids := ids) (t := ()) (8 : Nat)))
      (.cons recursiveCallees relatedArgs)
  have outputs : TupleRelated machine ids (number 9) (number 9) :=
    .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) (9 : Nat)) .nil
  have locals : LocalsRelated machine ids memberVertices storedL storedR :=
    ((LocalsRelated.empty (m := machine) (ids := ids) (rename := memberVertices)).emptyRight.snoc
      memberVertices.injective rfl outputs).emptyLeft
  exact .resume (vertices := memberVertices) rfl (.ret _ _ rfl) entry locals outer

private def checkpointL : Config machine Nat [num] :=
  ⟨.eval (.call refL recursiveArgs) (savedL (savedL .halt)), 33⟩

private def checkpointR : Config machine Nat [num] :=
  ⟨.eval (.call refR recursiveArgs) (savedR (savedR .halt)), 33⟩

private theorem reachedL : recursivePrefix recursiveL.toGraph = some checkpointL := by cbv
private theorem reachedR : recursivePrefix recursiveR.toGraph = some checkpointR := by cbv

private def enteredL : Config machine Nat [num] :=
  ⟨.eval (Job.openClosure machine refL recursiveArgs) (savedL (savedL .halt)), 33⟩

private def enteredR : Config machine Nat [num] :=
  ⟨.eval (Job.openClosure machine refR recursiveArgs) (savedR (savedR .halt)), 33⟩

private theorem enteredPair : Live machine ids Nat [num] enteredL enteredR :=
  RecursiveCall.open_related recursiveCallees relatedArgs selectedSchedule (savedPair (savedPair .halt)) 33

-- Dispatch from the real runner checkpoints. Both saved suffixes stay live.
example : recursivePrefix recursiveL.toGraph = some checkpointL ∧
    recursivePrefix recursiveR.toGraph = some checkpointR ∧
    Continuation.Partial.Step primitives checkpointL enteredL ∧
    Continuation.Partial.Step primitives checkpointR enteredR ∧
    Live machine ids Nat [num] enteredL enteredR :=
  ⟨reachedL, reachedR, Continuation.Partial.Step.of_next_some rfl,
    Continuation.Partial.Step.of_next_some rfl, enteredPair⟩

-- On repeated entry, the right machine passes a γ before reaching the
-- aligned primitive, while the left machine reaches it in one microstep.
example : Advance primitives ids enteredL enteredR := by
  apply RecursiveCall.advance respects enteredPair
  intro _ _ _ _ _ _ _ _ left _
  cases left

example : Advance primitives ids checkpointL checkpointR :=
  RecursiveCall.advance respects (.call 33 recursiveCallees relatedArgs (savedPair (savedPair .halt)))
    (DispatchReady.call selectedSchedule)

private def finishOperands {ins outs : Ports T} (opcode : Op ins outs)
    (input : Tuple machine.Val ins) : Option (Nat × Nat) :=
  match opcode with
  | .seed | .gain => none
  | .finish =>
    let .global _ source _ := input.get .head
    let .data flag := input.get (.tail .head)
    some (source, flag)

private def soleFrameVertex {ports : Ports T} : Stack machine ports [num] → Option Nat
  | .resume (past := past) _ _ _ .halt => some past.length
  | _ => none

private def blockedAttempt :
    Continuation.Partial.Executable.Observation machine Nat [num] → Option (Nat × Nat × Nat × Nat)
  | .blocked active store => do
    let vertex ← soleFrameVertex active.stack
    let (source, flag) ← finishOperands active.site.opcode active.site.input
    some (vertex, source, flag, store)
  | _ => none

private def selectedBlock {sigs : List (Ports T)} (graph : Omega Op args [fn.port] sigs) :
    Option (Nat × Nat × Nat × Nat) :=
  let callArgs : Tuple machine.Val fn.args := .cons (.data (0 : Nat)) (.cons (.control 0) .nil)
  (Executable.run actions 10 73 graph (number 1) .head callArgs 20).toOption.bind blockedAttempt

-- The selected undefined primitive has its own pending suffix. Its
-- address and captured global relocate, with the same flag and store.
example : selectedBlock recursiveL.toGraph = some (0, 0, 0, 23) := by cbv
example : selectedBlock recursiveR.toGraph = some (1, 1, 0, 23) := by cbv

open RecursiveCall (Family TupleIn Closed ClosedFamily Admitted)
open Continuation.Partial (Step)
open Relation (ReflTransGen TransGen)

-- One actual member is the only admissible callable on each side. The
-- family includes arbitrary ordinary data, controls and captured globals.
private inductive Supported {fn : Function Unit Unit} (member : machine.Val fn.port) : Family machine where
  | number (n : Nat) : Supported member (.data (t := ()) n)
  | capture (unit vertex n : Nat) : Supported member (.global unit vertex (.data (t := ()) n))
  | control {n : Nat} (tag : Fin n) : Supported member (.control tag)
  | self : Supported member member

private theorem numberIn {fn : Function Unit Unit} {member : machine.Val fn.port} (output : Tuple machine.Val [num]) :
    TupleIn (Supported member) output := by
  cases output with
  | cons value tail =>
    cases value with
    | data n =>
      cases tail
      exact ⟨.number n, trivial⟩

private theorem primitivesClosed {fn : Function Unit Unit} (member : machine.Val fn.port)
    (captures : ∀ {args outs : Ports T} {ref : machine.Val (.value (.function args outs))},
      Supported member ref → TupleIn (Supported member) (resolve machine ref).values) :
    Closed primitives (Supported member) where
  captures := captures
  primitive := by
    intro _ _ opcode _ _ _ _ output _
    cases opcode <;> exact numberIn output

private theorem supportedFamily : ClosedFamily primitives ids (Supported refL) (Supported refR) where
  closedL := primitivesClosed refL (by
    intro _ _ _ member
    cases member
    exact ⟨.capture 73 0 8, .self, trivial⟩)
  closedR := primitivesClosed refR (by
    intro _ _ _ member
    cases member
    exact ⟨.capture 73 1 8, .self, trivial⟩)
  schedule := by
    intro _ _ _ _ left right _
    cases left
    cases right
    exact selectedSchedule

private def invocation (ref : machine.Val fn.port) (stack : Stack machine [num] [num])
    (store : Nat) : Config machine Nat [num] :=
  ⟨.eval (.call ref recursiveArgs) stack, store⟩

private theorem callSegment (stack : Stack machine [num] [num]) (store : Nat) :
    TransGen (Step primitives) (invocation refL stack store) (invocation refL (savedL stack) (store + 5)) := by
  let entry : Config machine Nat [num] := ⟨.eval (Job.openClosure machine refL recursiveArgs) stack, store⟩
  have entered : Step primitives (invocation refL stack store) entry := Step.of_next_some rfl
  have more := Continuation.Partial.Executable.runFor_reachable actions 9 entry
  have checkpoint : runFor actions 9 entry = invocation refL (savedL stack) (store + 5) := by cbv
  exact TransGen.head' entered (checkpoint ▸ more)

private theorem productiveLeft : InfiniteTrace (Step primitives) (invocation refL .halt 23) := by
  apply InfiniteTrace.coinduct (fun cfg =>
    ∃ stack store, ReflTransGen (Step primitives) cfg (invocation refL stack store)) ?_ ⟨.halt, 23, .refl⟩
  rintro cfg ⟨stack, store, path⟩
  obtain ⟨next, picked, rest⟩ := TransGen.head'_iff.mp (TransGen.trans_right path (callSegment stack store))
  exact ⟨next, picked, savedL stack, store + 5, rest⟩

private theorem admittedExports :
    Admitted machine ids (Supported refL) (Supported refR) (invocation refL .halt 23) (invocation refR .halt 23) :=
  Admitted.call recursiveCallees relatedArgs .self .self
    ⟨.number 1, .control 0, trivial⟩ ⟨.number 1, .control 0, trivial⟩ 23

-- These are actual starts from the linked export. Every recursive
-- activation adds a pending non-tail frame and changes the store by five.
example : ∃ sourceL sourceR,
    Executable.start actions 73 recursiveL.toGraph (number 1) .head recursiveArgs 20 = .ok sourceL ∧
    Executable.start actions 73 recursiveR.toGraph (number 1) .head recursiveArgs 20 = .ok sourceR ∧
    InfiniteTrace (Step primitives) sourceL ∧ InfiniteTrace (Step primitives) sourceR := by
  refine ⟨invocation refL .halt 23, invocation refR .halt 23, ?_, ?_, productiveLeft, ?_⟩
  · cbv
  · cbv
  · exact (ClosedFamily.infinite_iff respects supportedFamily admittedExports).mp productiveLeft

private def blockedArgs : Tuple machine.Val fn.args := .cons (.data (0 : Nat)) (.cons (.control 0) .nil)

private def blockingEntry (ref : machine.Val fn.port) : Config machine Nat [num] :=
  ⟨Continuation.start (.call ref blockedArgs), 23⟩

private theorem relatedBlockedArgs : TupleRelated machine ids blockedArgs blockedArgs :=
  .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) (0 : Nat)) (.cons (.control 0) .nil)

private theorem admittedBlocking :
    Admitted machine ids (Supported refL) (Supported refR) (blockingEntry refL) (blockingEntry refR) :=
  Admitted.call recursiveCallees relatedBlockedArgs .self .self
    ⟨.number 0, .control 0, trivial⟩ ⟨.number 0, .control 0, trivial⟩ 23

-- Reflect the actual left runner endpoint into a matched pair of
-- terminal configurations, including the precise right blocked attempt.
example : ∃ endR,
    RecursiveCall.ReachedTerminal primitives ids (blockingEntry refL) (blockingEntry refR)
      (runFor actions 10 (blockingEntry refL)) endR ∧ endR.Blocked primitives := by
  apply (ClosedFamily.blocks respects supportedFamily admittedBlocking).1
  · exact Continuation.Partial.Executable.runFor_reachable actions 10 (blockingEntry refL)
  · exact ⟨_, by cbv, by cbv⟩

private abbrev control : T := .control 2
private abbrev branchFn : Function Unit Unit := ⟨[num, control, control], [num]⟩
private abbrev capturedWith (capture : T) : Ports T := [capture, branchFn.port, num, control]
private abbrev branchEntryWith (capture : T) : Ports T := [capture, branchFn.port, num, control, control]
private abbrev captured := capturedWith global

private abbrev finishNode {past : List (Ports T)} : NestedTheta.Node (Instruction Op) captured past [num] :=
  RecursiveCall.simple (.primitive Op.finish)
    (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil)) (fun i => i.elim0)

private abbrev inertNode {past : List (Ports T)} : NestedTheta.Node (Instruction Op) captured past [] :=
  RecursiveCall.emptyGamma (extra := 0) (entry := [])
    (.cons (.arg (.tail (.tail (.tail .head)))) .nil)

-- Only the administrative binding moves. The primitive that reads the
-- captured global is at vertex 0 on the left and vertex 1 on the right.
private def baseL : RecursiveCall.Code Op captured [] [[num], []] [num] :=
  .bind finishNode (fun i => i.elim0) <| .bind inertNode (fun _ => .ret .nil) <|
    .ret (.cons (.output (0 : Fin 2) .head) .nil)

private def baseR : RecursiveCall.Code Op captured [] [[], [num]] [num] :=
  .bind inertNode (fun _ => .ret .nil) <| .bind finishNode (fun i => i.elim0) <|
    .ret (.cons (.output (1 : Fin 2) .head) .nil)

private def addAfterWith {entry : Ports T} (opcode : Op [num] [num]) :
    RecursiveCall.Code Op entry [[num]] [[num]] [num] :=
  .bind (RecursiveCall.simple (.primitive opcode) (.cons (.output (0 : Fin 1) .head) .nil) (fun i => i.elim0))
    (fun i => i.elim0) (.ret (.cons (.output (1 : Fin 2) .head) .nil))

private abbrev addAfter {entry : Ports T} : RecursiveCall.Code Op entry [[num]] [[num]] [num] :=
  addAfterWith .seed

-- Pass the carried exit selector to the recursive call, then use its
-- returned tuple in a state-changing suffix.
private def recurArm {capture : T} : RecursiveCall.Code Op (capturedWith capture) [] [[num], [num]] [num] :=
  let after := Origin.arg (.tail (.tail (.tail .head))) (past := [])
  .bind (RecursiveCall.simple (.apply branchFn)
    (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) (.cons after (.cons after .nil))))
    (fun i => i.elim0)) (fun i => i.elim0) addAfter

private def branchWires {capture : T} : Wires (branchEntryWith capture) [] (control :: capturedWith capture) :=
  .cons (.arg (.tail (.tail (.tail .head))))
    (.cons (.arg .head) (.cons (.arg (.tail .head))
      (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail (.tail .head))))) .nil))))

private def branchSigs (sigs : List (Ports T)) : Fin 2 → List (Ports T) :=
  Fin.cases sigs fun _ => [[num], [num]]

private def branchChildren {capture : T} {sigs : List (Ports T)} (base : RecursiveCall.Code Op (capturedWith capture) [] sigs [num])
    (tag : Fin 2) : RecursiveCall.Code Op (capturedWith capture) [] (branchSigs sigs tag) [num] :=
  Fin.cases (n := 1) (motive := fun i => RecursiveCall.Code Op (capturedWith capture) [] (branchSigs sigs i) [num])
    base (fun _ => recurArm) tag

private def branchBodyWith {capture : T} {sigs : List (Ports T)}
    (base : RecursiveCall.Code Op (capturedWith capture) [] sigs [num]) (opcode : Op [num] [num]) :
    RecursiveCall.Code Op (branchEntryWith capture) [] [[num], [num]] [num] :=
  .bind (RecursiveCall.gammaNode (extra := 0) (entry := capturedWith capture) (outs := [num])
    branchWires (branchSigs sigs)) (branchChildren base) (addAfterWith opcode)

private abbrev branchBody {capture : T} {sigs : List (Ports T)}
    (base : RecursiveCall.Code Op (capturedWith capture) [] sigs [num]) :
    RecursiveCall.Code Op (branchEntryWith capture) [] [[num], [num]] [num] :=
  branchBodyWith base .seed

local instance : DecidableEq (Ty Unit Unit) := RecursiveCall.Numbered.decidePort

private def opcodeCode : NestedTheta.Equality.OpcodeCode Op where
  Key := Nat
  encode
    | .seed => 0
    | .finish => 1
    | .gain => 2
  injective := by
    intro _ _ x y equal
    cases x <;> cases y <;> first | rfl | cases equal

private abbrev instructionKeys := RecursiveCall.Numbered.instructionCode opcodeCode

private instance : DecidableEq instructionKeys.Key :=
  show DecidableEq (Sum Nat (Ports T × Ports T)) from inferInstance

private theorem baseIso : NestedTheta.Graph.Isomorphic (Instruction Op) baseL.toGraph baseR.toGraph := by
  refine .intro rfl rfl (Equiv.swap (0 : Fin 2) 1) ?_ ?_ rfl ?_
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · refine Fin.cases (fun i => i.elim0) (Fin.cases ?_ (fun i => i.elim0))
    intro arm
    exact NestedTheta.Graph.Isomorphic.refl _

private theorem branchBodyIso :
    NestedTheta.Graph.Isomorphic (Instruction Op) (branchBody baseL).toGraph (branchBody baseR).toGraph := by
  refine .intro rfl rfl (Equiv.refl _) ?_ ?_ rfl ?_
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases (Fin.cases baseIso (Fin.cases (NestedTheta.Graph.Isomorphic.refl _) (fun i => i.elim0)))
      (Fin.cases (fun i => i.elim0) (fun i => i.elim0))

private def branchGroupL := selfGroup branchFn (.output (0 : Fin 1) .head : Origin args [[global]] global)
  (branchBody baseL)
private def branchGroupR := selfGroup branchFn (.output (1 : Fin 2) .head : Origin args [[], [global]] global)
  (branchBody baseR)

private def branchModuleL : OmegaTerm Op args [branchFn.port] [[global], [branchFn.port], []] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.phi branchGroupL) <| .bind (.phi (emptyPhi Op args _)) <|
    .ret (.cons (.output (1 : Fin 3) .head) .nil)⟩

private def branchModuleR : OmegaTerm Op args [branchFn.port] [[], [global], [branchFn.port]] :=
  ⟨.bind (.phi (emptyPhi Op args [])) <| .bind (.delta (seedDelta [[]])) <| .bind (.phi branchGroupR) <|
    .ret (.cons (.output (2 : Fin 3) .head) .nil)⟩

private def branchRefL : machine.Val branchFn.port :=
  .member (.cons (globalValue 0 8) .nil) branchGroupL.toGraph.definitions 0

private def branchRefR : machine.Val branchFn.port :=
  .member (.cons (globalValue 1 8) .nil) branchGroupR.toGraph.definitions 0

private theorem branchGroupsIso : branchGroupL.Renumbered (renameVertex positions) branchGroupR :=
  ⟨⟨rfl, rfl⟩, Fin.cases ⟨⟨rfl, rfl⟩, branchBodyIso⟩ (fun i => i.elim0)⟩

private theorem branchModulesIso : branchModuleL.toGraph.RenumberedBy branchModuleR.toGraph positions :=
  (branchModuleL.renumberedBy_toGraph_iff branchModuleR positions).2
    ⟨Fin.cases (.delta ⟨⟨rfl, rfl⟩, noChildren_refl _ (fun i => Fin.cases rfl (fun j => j.elim0) i)⟩)
      (Fin.cases (.phi branchGroupsIso) (Fin.cases (.phi ⟨⟨rfl, rfl⟩, fun i => i.elim0⟩) (fun i => i.elim0))), rfl⟩

private theorem branchOrder : Ordered Op (renameVertex positions) args [branchFn.port]
    branchModuleL.toGraph.toTerm.region branchModuleR.toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .emptyRight (.bind rfl (.delta ⟨rfl, rfl⟩ seedTerm)
    (.bind rfl (.phi branchGroupsIso) (.emptyLeft (.ret _ _))))

private theorem branchOutcomes : OutcomesRelated machine ids Nat (renameVertex positions) [branchFn.port]
    (.linked (.cons branchRefL .nil) 23) (.linked (.cons branchRefR .nil) 23) := by
  have imports : TupleRelated machine ids (number 1) (number 1) :=
    .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) (1 : Nat)) .nil
  have linked := link_related (unitL := 73) (unitR := 73) respects branchModulesIso branchOrder
    (fun _ => ⟨rfl, rfl⟩) imports 20
  have left : link primitives 73 branchModuleL.toGraph (number 1) 20 = .linked (.cons branchRefL .nil) 23 :=
    (Executable.link_eq actions 73 branchModuleL.toGraph (number 1) 20).symm.trans (by cbv)
  have right : link primitives 73 branchModuleR.toGraph (number 1) 20 = .linked (.cons branchRefR .nil) 23 :=
    (Executable.link_eq actions 73 branchModuleR.toGraph (number 1) 20).symm.trans (by cbv)
  rwa [left, right] at linked

private theorem ordinaryOutputs : RecursiveCall.Numbered.OrdinaryOutputs Op := by
  intro _ _ opcode
  cases opcode <;> rfl

set_option maxHeartbeats 800000 in
private theorem branchAccepted :
    RecursiveCall.Numbered.checkExport instructionKeys branchRefL branchRefR = true := by
  simp only [RecursiveCall.Numbered.checkExport, branchRefL, branchRefR,
    RecursiveCall.Numbered.exportGroup, RecursiveCall.Numbered.checkGroupPair,
    RecursiveCall.Numbered.isStandaloneLambda]
  cbv

private theorem branchAdmission :
    RecursiveCall.Numbered.ExportAdmission primitives ids branchRefL branchRefR :=
  RecursiveCall.Numbered.checkExport_sound ordinaryOutputs branchAccepted

-- The linked member captures an imported function from outside its own
-- group. This origin is unsupported even though the body ignores it.
private abbrev unitFn : Function Unit Unit := ⟨[], []⟩

private def externalCaptureGroup : PhiTerm Op [branchFn.port] [] [unitFn] :=
  ⟨[branchFn.port], .cons (.arg .head) .nil, .cons ⟨[], .nil, [], .ret .nil⟩ .nil⟩

private def externalCaptureModule : OmegaTerm Op [branchFn.port] [unitFn.port] [[unitFn.port]] :=
  ⟨.bind (.phi externalCaptureGroup) (.ret (.cons (.output (0 : Fin 1) .head) .nil))⟩

example : match Executable.link actions 74 externalCaptureModule.toGraph (.cons branchRefL .nil) 23 with
    | .linked exports _ =>
      (RecursiveCall.Numbered.admitExport instructionKeys primitives ids ordinaryOutputs
        (exports.get .head) (exports.get .head)).isSome = false
    | .undefined _ => False := by cbv

private def branchArgs (flag : Nat) : Tuple machine.Val branchFn.args :=
  .cons (.data flag) (.cons (.control 1) (.cons (.control 0) .nil))

private def branchStart (ref : machine.Val branchFn.port) (flag : Nat) : Config machine Nat [num] :=
  ⟨Continuation.start (.call ref (branchArgs flag)), 23⟩

private theorem branchAdmitted (flag : Nat) :
    ∃ familyL familyR, ClosedFamily primitives ids familyL familyR ∧
      Admitted machine ids familyL familyR (branchStart branchRefL flag) (branchStart branchRefR flag) := by
  have inputs : TupleRelated machine ids (branchArgs flag) (branchArgs flag) :=
    .cons (ValueRelated.data (m := machine) (ids := ids) (t := ()) flag)
      (.cons (.control 1) (.cons (.control 0) .nil))
  exact branchAdmission.atExport .head branchOutcomes inputs rfl

private theorem branchLinkedL (flag : Nat) :
    Executable.start actions 73 branchModuleL.toGraph (number 1) .head (branchArgs flag) 20 =
      .ok (branchStart branchRefL flag) := by cbv

private theorem branchLinkedR (flag : Nat) :
    Executable.start actions 73 branchModuleR.toGraph (number 1) .head (branchArgs flag) 20 =
      .ok (branchStart branchRefR flag) := by cbv

-- Arm 1 recurses into arm 0. After the primitive, all three suffixes run
-- (the child join, the recursive arm, and the outer join).
example : Executable.run actions 40 73 branchModuleL.toGraph (number 1) .head (branchArgs 1) 20 =
    .ok (.returned (number 30) 37) := by cbv

example : ∃ sourceL sourceR endR,
    Executable.start actions 73 branchModuleL.toGraph (number 1) .head (branchArgs 1) 20 = .ok sourceL ∧
    Executable.start actions 73 branchModuleR.toGraph (number 1) .head (branchArgs 1) 20 = .ok sourceR ∧
    ReflTransGen (Step primitives) sourceR endR ∧ endR.result = some (number 30, 37) := by
  have reached := Continuation.Partial.Executable.runFor_reachable actions 40 (branchStart branchRefL 1)
  have result : (runFor actions 40 (branchStart branchRefL 1)).result = some (number 30, 37) := by cbv
  obtain ⟨_, _, closed, admitted⟩ := branchAdmitted 1
  obtain ⟨endR, valueR, path, got, values⟩ :=
    (ClosedFamily.returns respects closed admitted).1 _ _ _ reached result
  cases values with
  | cons paired tail =>
    cases paired
    cases tail
    exact ⟨_, _, endR, branchLinkedL 1, branchLinkedR 1, path, got⟩

private def savedVertices {ports results : Ports T} : Stack machine ports results → List Nat
  | .halt => []
  | .resume (past := past) _ _ _ outer => past.length :: savedVertices outer
  | .loop _ outer => savedVertices outer

private def branchAttempt :
    Continuation.Partial.Executable.Observation machine Nat [num] → Option (List Nat × Nat × Nat × Nat)
  | .blocked active store => do
    let (source, flag) ← finishOperands active.site.opcode active.site.input
    some (savedVertices active.stack, source, flag, store)
  | _ => none

-- At the undefined attempt the primitive, both γ joins and the recursive
-- application still have their actual frames. Only the inner site moves.
example : (Executable.run actions 40 73 branchModuleL.toGraph (number 1) .head (branchArgs 0) 20
    |>.toOption.bind branchAttempt) = some ([0, 0, 0, 0], 0, 0, 23) := by cbv

example : (Executable.run actions 40 73 branchModuleR.toGraph (number 1) .head (branchArgs 0) 20
    |>.toOption.bind branchAttempt) = some ([1, 0, 0, 0], 1, 0, 23) := by cbv

example : ∃ sourceL sourceR endR,
    Executable.start actions 73 branchModuleL.toGraph (number 1) .head (branchArgs 0) 20 = .ok sourceL ∧
    Executable.start actions 73 branchModuleR.toGraph (number 1) .head (branchArgs 0) 20 = .ok sourceR ∧
    RecursiveCall.ReachedTerminal primitives ids sourceL sourceR (runFor actions 40 sourceL) endR ∧
    endR.Blocked primitives := by
  obtain ⟨_, _, closed, admitted⟩ := branchAdmitted 0
  obtain ⟨endR, pair, blocked⟩ := (ClosedFamily.blocks respects closed admitted).1 _
    (Continuation.Partial.Executable.runFor_reachable actions 40 (branchStart branchRefL 0))
    ⟨_, by cbv, by cbv⟩
  exact ⟨_, _, endR, branchLinkedL 0, branchLinkedR 0, pair, blocked⟩

-- The exported λ reads an earlier φ binding. The call's returned value is
-- consumed by the λ's own state-changing suffix.
private abbrev wrappedInput : Ports T := branchFn.port :: branchFn.args

private def wrapWith {sigs : List (Ports T)} (suffix : RecursiveCall.Code Op wrappedInput [[num]] sigs [num]) :
    RecursiveCall.Code Op wrappedInput [] ([num] :: sigs) [num] :=
  .bind (RecursiveCall.simple (.apply branchFn)
    (.cons (.arg .head) (.cons (.arg (.tail .head))
      (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail (.tail .head)))) .nil))))
    (fun i => i.elim0)) (fun i => i.elim0) suffix

private def wrapperCode : RecursiveCall.Code Op wrappedInput [] [[num], [num]] [num] :=
  wrapWith addAfter

private def wrapper {past : List (Ports T)} (capture : Origin args past branchFn.port) :
    LambdaTerm Op args past branchFn :=
  ⟨[branchFn.port], .cons capture .nil, _, wrapperCode⟩

private def wrapperL := wrapper (.output (1 : Fin 3) .head :
  Origin args [[global], [branchFn.port], []] branchFn.port)

private def wrapperR := wrapper (.output (2 : Fin 3) .head :
  Origin args [[], [global], [branchFn.port]] branchFn.port)

private def wrappedL : OmegaTerm Op args [branchFn.port] [[global], [branchFn.port], [], [branchFn.port]] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.phi branchGroupL) <| .bind (.phi (emptyPhi Op args _)) <|
    .bind (.lambda wrapperL) <| .ret (.cons (.output (3 : Fin 4) .head) .nil)⟩

private def wrappedRWith (group : PhiTerm Op args [[], [global]] [branchFn]) :
    OmegaTerm Op args [branchFn.port] [[], [global], [branchFn.port], [branchFn.port]] :=
  ⟨.bind (.phi (emptyPhi Op args [])) <| .bind (.delta (seedDelta [[]])) <| .bind (.phi group) <|
    .bind (.lambda wrapperR) <| .ret (.cons (.output (3 : Fin 4) .head) .nil)⟩

private abbrev wrappedR := wrappedRWith branchGroupR

private def wrapperRef (ref : machine.Val branchFn.port) : machine.Val branchFn.port :=
  .closure (.cons ref .nil) wrapperCode.toGraph

private def wrappedPositions : Fin 4 ≃ Fin 4 := (Equiv.swap 0 1).trans (Equiv.swap 0 2)

private def wrappedIds : GlobalRel := fun left right =>
  left.1 = right.1 ∧ renameVertex wrappedPositions left.2 = right.2

private theorem wrappedGroupsIso : branchGroupL.Renumbered (renameVertex wrappedPositions) branchGroupR :=
  ⟨⟨rfl, rfl⟩, Fin.cases ⟨⟨rfl, rfl⟩, branchBodyIso⟩ (fun i => i.elim0)⟩

private theorem wrapperIso : wrapperL.Renumbered (renameVertex wrappedPositions) wrapperR :=
  ⟨⟨rfl, rfl⟩, NestedTheta.Graph.Isomorphic.refl _⟩

private theorem wrappedIso : wrappedL.toGraph.RenumberedBy wrappedR.toGraph wrappedPositions :=
  (wrappedL.renumberedBy_toGraph_iff wrappedR wrappedPositions).2
    ⟨Fin.cases (.delta ⟨⟨rfl, rfl⟩, noChildren_refl _ (fun i => Fin.cases rfl (fun j => j.elim0) i)⟩)
      (Fin.cases (.phi wrappedGroupsIso) (Fin.cases (.phi ⟨⟨rfl, rfl⟩, fun i => i.elim0⟩)
        (Fin.cases (.lambda wrapperIso) (fun i => i.elim0)))), rfl⟩

private theorem wrappedOrder : Ordered Op (renameVertex wrappedPositions) args [branchFn.port]
    wrappedL.toGraph.toTerm.region wrappedR.toGraph.toTerm.region := by
  rw [OmegaTerm.toTerm_toGraph, OmegaTerm.toTerm_toGraph]
  exact .emptyRight (.bind rfl (.delta ⟨rfl, rfl⟩ seedTerm)
    (.bind rfl (.phi wrappedGroupsIso) (.emptyLeft (.bind rfl (.lambda wrapperIso) (.ret _ _)))))

private theorem wrappedLinkL : Executable.link actions 73 wrappedL.toGraph (number 1) 20 =
    .linked (.cons (wrapperRef branchRefL) .nil) 23 := by cbv

private theorem wrappedLinkR : Executable.link actions 73 wrappedR.toGraph (number 1) 20 =
    .linked (.cons (wrapperRef branchRefR) .nil) 23 := by cbv

private theorem wrappedOutcomes : OutcomesRelated machine wrappedIds Nat (renameVertex wrappedPositions) [branchFn.port]
    (.linked (.cons (wrapperRef branchRefL) .nil) 23) (.linked (.cons (wrapperRef branchRefR) .nil) 23) := by
  have imports : TupleRelated machine wrappedIds (number 1) (number 1) :=
    .cons (ValueRelated.data (m := machine) (ids := wrappedIds) (t := ()) (1 : Nat)) .nil
  have linked := link_related (unitL := 73) (unitR := 73) (respectsGlobals wrappedIds) wrappedIso wrappedOrder
    (fun _ => ⟨rfl, rfl⟩) imports 20
  have left : link primitives 73 wrappedL.toGraph (number 1) 20 = _ :=
    (Executable.link_eq actions 73 wrappedL.toGraph (number 1) 20).symm.trans wrappedLinkL
  have right : link primitives 73 wrappedR.toGraph (number 1) 20 = _ :=
    (Executable.link_eq actions 73 wrappedR.toGraph (number 1) 20).symm.trans wrappedLinkR
  rwa [left, right] at linked

private theorem wrappersCheckMember (left right : RecursiveCall.Numbered.Group machine [branchFn]) :
    RecursiveCall.Numbered.checkExport instructionKeys (wrapperRef (left.ref 0)) (wrapperRef (right.ref 0)) =
      RecursiveCall.Numbered.checkExport instructionKeys (left.ref 0) (right.ref 0) := by
  have bodies : (RecursiveCall.Numbered.inferResolved instructionKeys
      (resolve machine (wrapperRef (left.ref 0))) (resolve machine (wrapperRef (right.ref 0)))).isSome = true := by cbv
  change (RecursiveCall.Numbered.checkGroupPair instructionKeys left right && _) =
    RecursiveCall.Numbered.checkGroupPair instructionKeys left right
  rw [bodies, Bool.and_true]

private theorem wrappedAccepts : RecursiveCall.Numbered.checkExport instructionKeys
    (wrapperRef branchRefL) (wrapperRef branchRefR) = true :=
  (wrappersCheckMember ⟨_, _, _⟩ ⟨_, _, _⟩).trans branchAccepted

private theorem wrappedAdmission :
    RecursiveCall.Numbered.ExportAdmission primitives wrappedIds (wrapperRef branchRefL) (wrapperRef branchRefR) :=
  RecursiveCall.Numbered.checkExport_sound ordinaryOutputs wrappedAccepts

-- A φ member alone returns 30 at store 37. The actual λ export resumes
-- its saved suffix after that call and returns 37 at store 40.
example : Executable.run actions 60 73 wrappedL.toGraph (number 1) .head (branchArgs 1) 20 =
    .ok (.returned (number 37) 40) := by cbv

example :
    ∃ target, ReflTransGen (Step primitives) (branchStart (wrapperRef branchRefR) 1) target ∧
      target.result = some (number 37, 40) := by
  have inputs : TupleRelated machine wrappedIds (branchArgs 1) (branchArgs 1) :=
    .cons (ValueRelated.data (m := machine) (ids := wrappedIds) (t := ()) (1 : Nat))
      (.cons (.control 1) (.cons (.control 0) .nil))
  obtain ⟨_, _, closed, admitted⟩ := wrappedAdmission.atExport .head wrappedOutcomes inputs rfl
  have reached := Continuation.Partial.Executable.runFor_reachable actions 60 (branchStart (wrapperRef branchRefL) 1)
  have result : (runFor actions 60 (branchStart (wrapperRef branchRefL) 1)).result = some (number 37, 40) := by cbv
  obtain ⟨target, valueR, path, got, values⟩ :=
    (ClosedFamily.returns (respectsGlobals wrappedIds) closed admitted).1 _ _ _ reached result
  cases values with
  | cons paired tail =>
    cases paired
    cases tail
    exact ⟨target, path, got⟩

private def foreignGroup :=
  selfGroup branchFn (.output (1 : Fin 2) .head : Origin args [[], [global]] global)
    (.ret (.cons (.arg (.tail (.tail .head))) .nil) : RecursiveCall.Code Op (branchEntryWith global) [] [] [num])

private def foreignRef : machine.Val branchFn.port :=
  .member (.cons (globalValue 1 8) .nil) foreignGroup.toGraph.definitions 0

private theorem foreignLinks : Executable.link actions 73 (wrappedRWith foreignGroup).toGraph (number 1) 20 =
    .linked (.cons (wrapperRef foreignRef) .nil) 23 := by cbv

set_option maxHeartbeats 800000 in
private theorem foreignMemberRejected :
    RecursiveCall.Numbered.checkExport instructionKeys branchRefL foreignRef = false := by
  simp only [RecursiveCall.Numbered.checkExport, RecursiveCall.Numbered.isStandaloneLambda,
    RecursiveCall.Numbered.exportGroup, branchRefL, foreignRef, RecursiveCall.Numbered.checkGroupPair]
  cbv

private theorem foreignRejected : RecursiveCall.Numbered.checkExport instructionKeys
    (wrapperRef branchRefL) (wrapperRef foreignRef) = false :=
  (wrappersCheckMember ⟨_, _, _⟩ ⟨_, _, _⟩).trans foreignMemberRejected

-- Both links succeed. The right λ captured a different, same-signature
-- φ implementation, so checking the λ bodies alone cannot admit this pair.
example : match Executable.link actions 73 wrappedL.toGraph (number 1) 20,
    Executable.link actions 73 (wrappedRWith foreignGroup).toGraph (number 1) 20 with
  | .linked exportsL _, .linked exportsR _ =>
    (RecursiveCall.Numbered.admitExport instructionKeys primitives wrappedIds ordinaryOutputs
      (exportsL.get .head) (exportsR.get .head)).isSome = false
  | _, _ => False := by
  rw [wrappedLinkL, foreignLinks]
  change (RecursiveCall.Numbered.admitExport instructionKeys primitives wrappedIds ordinaryOutputs
    (wrapperRef branchRefL) (wrapperRef foreignRef)).isSome = false
  simp [RecursiveCall.Numbered.admitExport, foreignRejected]

open RecursiveCall.Numbered (linkedLambda)
open RecursiveCall.Numbered.Prefix (GraphPlan Plan admit admitGraph)

private abbrev prefixL : List (Ports T) := [[global], [branchFn.port], []]
private abbrev prefixR : List (Ports T) := [[], [global], [branchFn.port]]

private def beforeWrapperL : Locals machine.Val prefixL :=
  (.cons (globalValue 0 8) .nil, .cons branchRefL .nil, .nil, PUnit.unit)

private def beforeWrapperR : Locals machine.Val prefixR :=
  (.nil, .cons (globalValue 1 8) .nil, .cons branchRefR .nil, PUnit.unit)

private abbrev combinedInput : Ports T := [branchFn.port, branchFn.port] ++ branchFn.args

private def combinedBody : RecursiveCall.Code Op combinedInput [] [[num], [num], [num]] [num] :=
  let mode : Port combinedInput control := .tail (.tail (.tail .head))
  let after : Port combinedInput control := .tail (.tail (.tail (.tail .head)))
  let first := RecursiveCall.simple (.apply branchFn)
    (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) (.cons (.arg mode) (.cons (.arg after) .nil))))
    (fun i => i.elim0)
  let second : NestedTheta.Node (Instruction Op) combinedInput [[num]] [num] :=
    RecursiveCall.simple (.apply branchFn)
    (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 1) .head) (.cons (.arg mode) (.cons (.arg after) .nil))))
    (fun i => i.elim0)
  let suffix : NestedTheta.Node (Instruction Op) combinedInput [[num], [num]] [num] :=
    RecursiveCall.simple (.primitive Op.seed) (.cons (.output (1 : Fin 2) .head) .nil) (fun i => i.elim0)
  .bind first (fun i => i.elim0) <| .bind second (fun i => i.elim0) <| .bind suffix (fun i => i.elim0) <|
    .ret (.cons (.output (2 : Fin 3) .head) .nil)

-- This earlier λ has the same signature but was left out of the checked
-- prefix. The linker can still construct it and pass it on a capture wire.
private def uncheckedLambda {past : List (Ports T)} : LambdaTerm Op args past branchFn :=
  ⟨[], .nil, [], .ret (.cons (.arg .head) .nil)⟩

private def uncheckedRef : machine.Val branchFn.port :=
  .closure (.nil : Tuple machine.Val []) (uncheckedLambda (past := [])).body.toGraph

private abbrev combinedPastL := prefixL ++ [[branchFn.port], [branchFn.port]]
private abbrev combinedPastR := prefixR ++ [[branchFn.port], [branchFn.port]]

private def combined {past : List (Ports T)} (first second : Origin args past branchFn.port) :
    LambdaTerm Op args past branchFn :=
  ⟨[branchFn.port, branchFn.port], .cons first (.cons second .nil), _, combinedBody⟩

private def combinedL : LambdaTerm Op args combinedPastL branchFn :=
  combined (.output (3 : Fin 5) .head) (.output (1 : Fin 5) .head)

private def combinedR : LambdaTerm Op args combinedPastR branchFn :=
  combined (.output (3 : Fin 5) .head) (.output (2 : Fin 5) .head)

private def combinedBad : LambdaTerm Op args combinedPastR branchFn :=
  combined (.output (3 : Fin 5) .head) (.output (4 : Fin 5) .head)

private def combinedModuleLWith (second : LambdaTerm Op args (prefixL ++ [[branchFn.port]]) branchFn)
    (root : LambdaTerm Op args combinedPastL branchFn) :
    OmegaTerm Op args [branchFn.port] (combinedPastL ++ [[branchFn.port]]) :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.phi branchGroupL) <| .bind (.phi (emptyPhi Op args _)) <|
    .bind (.lambda wrapperL) <| .bind (.lambda second) <| .bind (.lambda root) <|
    .ret (.cons (.output (5 : Fin 6) .head) .nil)⟩

private def combinedModuleRWith (second : LambdaTerm Op args (prefixR ++ [[branchFn.port]]) branchFn)
    (root : LambdaTerm Op args combinedPastR branchFn) :
    OmegaTerm Op args [branchFn.port] (combinedPastR ++ [[branchFn.port]]) :=
  ⟨.bind (.phi (emptyPhi Op args [])) <| .bind (.delta (seedDelta [[]])) <| .bind (.phi branchGroupR) <|
    .bind (.lambda wrapperR) <| .bind (.lambda second) <| .bind (.lambda root) <|
    .ret (.cons (.output (5 : Fin 6) .head) .nil)⟩

private abbrev combinedModuleL := combinedModuleLWith uncheckedLambda combinedL
private abbrev combinedModuleR := combinedModuleRWith uncheckedLambda

private def combinedLocalsL : Locals machine.Val combinedPastL :=
  (beforeWrapperL.snoc (.cons (wrapperRef branchRefL) .nil)).snoc (.cons uncheckedRef .nil)

private def combinedLocalsR : Locals machine.Val combinedPastR :=
  (beforeWrapperR.snoc (.cons (wrapperRef branchRefR) .nil)).snoc (.cons uncheckedRef .nil)

private abbrev combinedRefL := linkedLambda combinedL.toGraph (number 1) combinedLocalsL
private abbrev combinedRefR := linkedLambda combinedR.toGraph (number 1) combinedLocalsR
private abbrev combinedRefBad := linkedLambda combinedBad.toGraph (number 1) combinedLocalsR

-- The plan selects the paired φ, the wrapper λ and the final λ, and
-- leaves the unrelated λ linked but unchecked on each side.
private def combinedPlan (root : LambdaTerm Op args combinedPastR branchFn) :
    Plan Op args args [branchFn.port] false combinedModuleL.region (combinedModuleR root).region :=
  .skipL (.skipR (.skipR (.seed (.skipL (.lambda (.skipL (.skipR (.lambda .done))))))))

private def combinedScan (root : LambdaTerm Op args combinedPastR branchFn) :=
  admit instructionKeys actions wrappedIds ordinaryOutputs 73 73 (number 1) (number 1)
    combinedModuleL (combinedModuleR root) (combinedPlan root) (fn := branchFn) .head 20 20

private theorem combinedLinkL : Executable.link actions 73 combinedModuleL.toGraph (number 1) 20 =
    .linked (.cons combinedRefL .nil) 23 := by cbv

private theorem combinedLinkR : Executable.link actions 73 (combinedModuleR combinedR).toGraph (number 1) 20 =
    .linked (.cons combinedRefR .nil) 23 := by cbv

private theorem combinedBadLinks : Executable.link actions 73 (combinedModuleR combinedBad).toGraph (number 1) 20 =
    .linked (.cons combinedRefBad .nil) 23 := by cbv

private theorem combinedOutcomes : OutcomesRelated machine wrappedIds Nat (renameVertex wrappedPositions)
    [branchFn.port] (Executable.link actions 73 combinedModuleL.toGraph (number 1) 20)
      (Executable.link actions 73 (combinedModuleR combinedR).toGraph (number 1) 20) := by
  rw [combinedLinkL, combinedLinkR]
  cases wrappedOutcomes with
  | linked wrapped =>
    have captures := (Recursive.resolve_related (wrapped.get .head)).1
    exact .linked (.cons (.closure (.cons (wrapped.get .head) captures) (NestedTheta.Graph.Isomorphic.refl _)) .nil) 23

set_option maxHeartbeats 800000 in
private theorem combinedAccepted : (combinedScan combinedR).isSome = true := by cbv

-- Both applications are non-tail. The first calls the earlier λ, the
-- second dispatches directly to φ with the first call's returned data.
example : Executable.run actions 100 73 combinedModuleL.toGraph (number 1) .head (branchArgs 1) 20 =
    .ok (.returned (number 37) 57) := by cbv

example :
    Executable.link actions 73 (combinedModuleR combinedR).toGraph (number 1) 20 =
      .linked (.cons combinedRefR .nil) 23 ∧
    ∃ target, ReflTransGen (Step primitives) (branchStart combinedRefR 1) target ∧
      target.result = some (number 37, 57) := by
  refine ⟨combinedLinkR, ?_⟩
  have accepted := ((combinedScan combinedR).get combinedAccepted).down
  change RecursiveCall.Numbered.Prefix.AdmittedExport primitives wrappedIds (fn := branchFn) .head
    (Executable.link actions 73 combinedModuleL.toGraph (number 1) 20)
    (Executable.link actions 73 (combinedModuleR combinedR).toGraph (number 1) 20) at accepted
  rw [combinedLinkL, combinedLinkR] at accepted
  have inputs : TupleRelated machine wrappedIds (branchArgs 1) (branchArgs 1) :=
    .cons (ValueRelated.data (m := machine) (ids := wrappedIds) (t := ()) (1 : Nat))
      (.cons (.control 1) (.cons (.control 0) .nil))
  have linked := combinedOutcomes
  rw [combinedLinkL, combinedLinkR] at linked
  obtain ⟨_, _, closed, admitted⟩ := accepted.atExport .head linked inputs rfl
  have reached := Continuation.Partial.Executable.runFor_reachable actions 100 (branchStart combinedRefL 1)
  have result : (runFor actions 100 (branchStart combinedRefL 1)).result = some (number 37, 57) := by cbv
  obtain ⟨target, valueR, path, got, values⟩ :=
    (ClosedFamily.returns (respectsGlobals wrappedIds) closed admitted).1 _ _ _ reached result
  cases values with
  | cons value tail =>
    cases value
    cases tail
    exact ⟨target, path, got⟩

-- The second capture has the same type, but row 4 was left unchecked.
set_option maxHeartbeats 800000 in
example :
    Executable.link actions 73 (combinedModuleR combinedBad).toGraph (number 1) 20 =
      .linked (.cons combinedRefBad .nil) 23 ∧
    (combinedScan combinedBad).isSome = false := by
  refine ⟨combinedBadLinks, ?_⟩
  cbv

-- The two earlier λs have the same signature, captured φ member, and
-- outer vertex count. Their state-changing primitives differ.
private def gainRow {past : List (Ports T)} (wire : Origin wrappedInput past num) :
    NestedTheta.Node (Instruction Op) wrappedInput past [num] :=
  RecursiveCall.simple (.primitive Op.gain) (.cons wire .nil) (fun i => i.elim0)

private def gainWrapperCode : RecursiveCall.Code Op wrappedInput [] [[num], [num]] [num] :=
  wrapWith (.bind (gainRow (.output (0 : Fin 1) .head)) (fun i => i.elim0)
    (.ret (.cons (.output (1 : Fin 2) .head) .nil)))

-- The extra empty γ is skipped when checking the two bodies in order.
-- It moves the gain primitive from vertex 1 to vertex 2.
private def paddedGainCode : RecursiveCall.Code Op wrappedInput [] [[num], [], [num]] [num] :=
  wrapWith (.bind (RecursiveCall.emptyGamma (extra := 0) (entry := [])
      (.cons (.arg (.tail (.tail .head))) .nil)) (fun _ => .ret .nil)
    (.bind (gainRow (.output (0 : Fin 2) .head)) (fun i => i.elim0)
      (.ret (.cons (.output (2 : Fin 3) .head) .nil))))

private def secondWrapper {past : List (Ports T)} (capture : Origin args past branchFn.port)
    (duplicate padded : Bool) : LambdaTerm Op args past branchFn :=
  if duplicate then wrapper capture
  else if padded then ⟨[branchFn.port], .cons capture .nil, _, paddedGainCode⟩
  else ⟨[branchFn.port], .cons capture .nil, _, gainWrapperCode⟩

private def bothL (duplicate : Bool) : OmegaTerm Op args [branchFn.port] (combinedPastL ++ [[branchFn.port]]) :=
  combinedModuleLWith (secondWrapper (.output (1 : Fin 4) .head) duplicate false)
    (combined (.output (3 : Fin 5) .head) (.output (4 : Fin 5) .head))

private def bothR (duplicate : Bool) (padded : Bool := false) :
    OmegaTerm Op args [branchFn.port] (combinedPastR ++ [[branchFn.port]]) :=
  combinedModuleRWith (secondWrapper (.output (2 : Fin 4) .head) duplicate padded) combinedBad

private def bothPlan (duplicate padded : Bool) : Plan Op args args [branchFn.port] false (bothL duplicate).region
    (bothR duplicate padded).region :=
  .skipL (.skipR (.skipR (.seed (.skipL (.lambda (.lambda (.lambda .done)))))))

private def bothScan (duplicate : Bool) (padded : Bool := false) :=
  admit instructionKeys actions wrappedIds ordinaryOutputs 73 73 (number 1) (number 1)
    (bothL duplicate) (bothR duplicate padded) (bothPlan duplicate padded) (fn := branchFn) .head 20 20

set_option maxHeartbeats 800000 in
example : (bothScan false).isSome = true := by cbv

set_option maxHeartbeats 800000 in
example : (bothScan false true).isSome = true := by cbv

-- Both calls return to the final λ. It passes the first result to the
-- second call and uses the second result in its own stateful suffix.
example :
    Executable.run actions 100 73 (bothL false).toGraph (number 1) .head (branchArgs 1) 20 =
      .ok (.returned (number 51) 63) ∧
    Executable.run actions 100 73 (bothR false).toGraph (number 1) .head (branchArgs 1) 20 =
      .ok (.returned (number 51) 63) ∧
    Executable.run actions 100 73 (bothR false true).toGraph (number 1) .head (branchArgs 1) 20 =
      .ok (.returned (number 51) 63) := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

private def duplicateExport (ref : machine.Val branchFn.port) : machine.Val branchFn.port :=
  .closure (.cons (wrapperRef ref) (.cons (wrapperRef ref) .nil)) combinedBody.toGraph

-- These distinct source bindings produce literally the same callable
-- value on each side. Both links succeed, but the body-based check
-- cannot use those values to separate the two prospective dispatches.
set_option maxHeartbeats 800000 in
example :
    Executable.link actions 73 (bothL true).toGraph (number 1) 20 =
      .linked (.cons (duplicateExport branchRefL) .nil) 23 ∧
    Executable.link actions 73 (bothR true).toGraph (number 1) 20 =
      .linked (.cons (duplicateExport branchRefR) .nil) 23 ∧
    (bothScan true).isSome = false := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

private def captureCode : RecursiveCall.Numbered.CaptureCode machine where
  Key := Nat
  decideKey := inferInstance
  data n := some n
  state _ := none

private abbrev sameBodyInput := global :: branchFn.args

private def sameBodyStep {past : List (Ports T)} :
    NestedTheta.Node (Instruction Op) sameBodyInput past [num] :=
  RecursiveCall.simple (.primitive Op.finish)
    (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) (fun i => i.elim0)

private def sameBody : RecursiveCall.Code Op sameBodyInput [] [[num]] [num] :=
  .bind sameBodyStep (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def paddedSameBody : RecursiveCall.Code Op sameBodyInput [] [[], [num]] [num] :=
  .bind (RecursiveCall.emptyGamma (extra := 0) (entry := [])
      (.cons (.arg (.tail (.tail .head))) .nil)) (fun _ => .ret .nil)
    (.bind sameBodyStep (fun i => i.elim0) (.ret (.cons (.output (1 : Fin 2) .head) .nil)))

private def sameBodyLambda {past : List (Ports T)} (source : Origin args past global)
    (padded : Bool := false) : LambdaTerm Op args past branchFn :=
  if padded then ⟨[global], .cons source .nil, _, paddedSameBody⟩
  else ⟨[global], .cons source .nil, _, sameBody⟩

private abbrev captureExports := [branchFn.port, branchFn.port, branchFn.port]

private def captureModule (duplicate : Bool) (paddedFirst : Bool := false) :
    OmegaTerm Op args captureExports [[global], [global], [], [branchFn.port], [branchFn.port], [branchFn.port]] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.delta finishL) <| .bind (.phi (emptyPhi Op args _)) <|
    .bind (.lambda (sameBodyLambda (.output (0 : Fin 3) .head) paddedFirst)) <|
    .bind (.lambda (sameBodyLambda (if duplicate then .output (0 : Fin 4) .head else .output (1 : Fin 4) .head))) <|
    .bind (.lambda (if duplicate then combined (.output (4 : Fin 5) .head) (.output (3 : Fin 5) .head)
      else combined (.output (3 : Fin 5) .head) (.output (4 : Fin 5) .head))) <|
    .ret (.cons (.output (3 : Fin 6) .head) (.cons (.output (4 : Fin 6) .head)
      (.cons (.output (5 : Fin 6) .head) .nil)))⟩

private def capturePlan (duplicate : Bool) :
    Plan Op args args captureExports false (captureModule duplicate).region (captureModule duplicate).region :=
  .skipL (.skipR (.skipL (.skipR (.seed (.lambda (.lambda (.lambda .done)))))))

private def captureScan (duplicate : Bool) (observer : RecursiveCall.Numbered.CaptureCode machine) :=
  admit instructionKeys actions Eq ordinaryOutputs 73 73 (number 1) (number 1)
    (captureModule duplicate) (captureModule duplicate) (capturePlan duplicate) (fn := branchFn)
    (.tail (.tail .head)) 20 20 observer

-- The initializers produce payloads 8 and 9. Both λs have the same
-- body, so the payload observation is what separates the two dispatches.
set_option maxHeartbeats 800000 in
example : (captureScan false captureCode).isSome = true ∧
    (captureScan false (.controlOnly machine)).isSome = false := by
  constructor <;> cbv

-- The actual caller passes the first result into the second application
-- and resumes its own stateful suffix after the two distinct calls.
example :
    Executable.run actions 60 73 (captureModule false).toGraph (number 1) .head (branchArgs 1) 20 =
      .ok (.returned (number 9) 33) ∧
    Executable.run actions 60 73 (captureModule false).toGraph (number 1) (.tail .head) (branchArgs 1) 20 =
      .ok (.returned (number 10) 33) ∧
    Executable.run actions 60 73 (captureModule false).toGraph (number 1) (.tail (.tail .head)) (branchArgs 1) 20 =
      .ok (.returned (number 17) 41) := by
  refine ⟨?_, ?_, ?_⟩ <;> cbv

-- The duplicate graph links with the same initialized value captured by
-- both closures. A plan requiring two separate dispatch entries rejects it.
set_option maxHeartbeats 800000 in
example : (match Executable.link actions 73 (captureModule true).toGraph (number 1) 20 with
    | .linked exports store => exports.get .head = exports.get (.tail .head) ∧ store = 28
    | .undefined _ => False) ∧ (captureScan true captureCode).isSome = false := by
  constructor
  · cbv
    exact ⟨rfl, trivial⟩
  · cbv

private def exactFirstOrder : RecursiveCall.Numbered.ExactValueCheck machine :=
  RecursiveCall.Numbered.ExactValueCheck.firstOrder (fun _ => inferInstanceAs (DecidableEq Nat))
    (fun _ => inferInstanceAs (DecidableEq Unit))

private def exactLambdas : RecursiveCall.Numbered.ExactValueCheck machine :=
  RecursiveCall.Numbered.ExactValueCheck.lambda instructionKeys exactFirstOrder

private def aliasPlan (duplicateL duplicateR : Bool) :
    Plan Op args args captureExports false (captureModule duplicateL).region (captureModule duplicateR).region :=
  .skipL (.skipR (.skipL (.skipR (.seed (.lambda (.alias 0 (.lambda .done)))))))

private def aliasScan (duplicateL duplicateR : Bool) (port : Port captureExports branchFn.port) :=
  admit instructionKeys actions Eq ordinaryOutputs 73 73 (number 1) (number 1)
    (captureModule duplicateL) (captureModule duplicateR) (aliasPlan duplicateL duplicateR) (fn := branchFn)
    port 20 20 (exactValue := exactLambdas)

-- The alias can be exported directly or captured alongside the earlier
-- binding. Both refer to the exact values entered by the actual linker.
#guard (aliasScan true true (.tail .head)).isSome
#guard (aliasScan true true (.tail (.tail .head))).isSome

-- A duplicate only on the left fails, as does an attempt to coalesce
-- equal-profile closures with distinct captures on both sides.
#guard (aliasScan true false (.tail (.tail .head))).isNone
#guard (aliasScan false false (.tail (.tail .head))).isNone

-- The caller invokes the alias first. At its undefined action the callee
-- and the caller suffix are pending. A suspended successful run can resume
-- from that same call and finish both applications and the caller suffix.
example : (Executable.run actions 60 73 (captureModule true).toGraph (number 1)
    (.tail (.tail .head)) (branchArgs 0) 20 |>.toOption.bind branchAttempt) =
      some ([0, 0], 0, 0, 28) := by cbv

example : (match Executable.run actions 5 73 (captureModule true).toGraph (number 1)
    (.tail (.tail .head)) (branchArgs 1) 20 with
  | .ok (.suspended config) => (runFor actions 60 config).result
  | _ => none) = some (number 16, 41) := by cbv

private abbrev scanExports := [branchFn.port, branchFn.port, branchFn.port, branchFn.port]

private abbrev scanCaller : Port scanExports branchFn.port := .tail (.tail (.tail .head))

private def scanModule (useSecond : Bool) :
    OmegaTerm Op args scanExports [[global], [global], [], [branchFn.port], [branchFn.port],
      [branchFn.port], [branchFn.port]] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.delta finishL) <| .bind (.phi (emptyPhi Op args _)) <|
    .bind (.lambda (sameBodyLambda (.output (0 : Fin 3) .head))) <|
    .bind (.lambda (sameBodyLambda (.output (1 : Fin 4) .head))) <|
    .bind (.lambda (sameBodyLambda (if useSecond then .output (1 : Fin 5) .head else .output (0 : Fin 5) .head))) <|
    .bind (.lambda (combined (.output (5 : Fin 6) .head) (.output (3 : Fin 6) .head))) <|
    .ret (.cons (.output (3 : Fin 7) .head) (.cons (.output (4 : Fin 7) .head)
      (.cons (.output (5 : Fin 7) .head) (.cons (.output (6 : Fin 7) .head) .nil))))⟩

private def scanPlan (left right : Bool) :
    Plan Op args args scanExports false (scanModule left).region (scanModule right).region :=
  .skipL (.skipR (.skipL (.skipR (.seed (.lambda (.lambda (.aliasFirst (.lambda .done))))))))

private def inferredAlias (left right : Bool) :=
  admit instructionKeys actions Eq ordinaryOutputs 73 73 (number 1) (number 1)
    (scanModule left) (scanModule right) (scanPlan left right) (fn := branchFn) scanCaller 20 20
    captureCode (exactValue := exactLambdas)

-- The first two bindings have the same body and distinct captured values.
-- The third row can alias either paired definition. Opposite choices have
-- one exact match per side, but those matches belong to different pairs.
#guard (inferredAlias false false).isSome
#guard (inferredAlias true true).isSome
#guard (inferredAlias false true).isNone

open RecursiveCall.Numbered.Prefix (LambdaEntry findAlias)

private def allLinkedValues : Family machine := fun {_} _ => True

private def linkedAliasIndex (useSecond : Bool) : Option Nat :=
  match Executable.link actions 73 (scanModule useSecond).toGraph (number 1) 20 with
  | .linked outputs _ =>
    let pair (port : Port scanExports branchFn.port) : LambdaEntry allLinkedValues allLinkedValues :=
      ⟨branchFn, outputs.get port, outputs.get port, trivial, trivial⟩
    let callee := outputs.get (.tail (.tail .head))
    (findAlias [pair (.tail .head), pair .head, pair .head] exactLambdas (fn := branchFn) callee callee).map
      fun hit => hit.index.val
  | .undefined _ => none

-- Test the returned index directly with real linker values, including a
-- repeated candidate so success at the first matching index is observable.
#guard linkedAliasIndex false == some 1
#guard linkedAliasIndex true == some 0

example : (Executable.run actions 60 73 (scanModule false).toGraph (number 1)
    scanCaller (branchArgs 0) 20 |>.toOption.bind branchAttempt) =
      some ([0, 0], 0, 0, 28) := by cbv

example : (match Executable.run actions 5 73 (scanModule false).toGraph (number 1)
    scanCaller (branchArgs 1) 20 with
  | .ok (.suspended config) => (runFor actions 60 config).result
  | _ => none) = some (number 16, 41) := by cbv

private def autoPlan (left right : Bool) :
    Plan Op args args scanExports false (scanModule left).region (scanModule right).region :=
  .skipL (.skipR (.skipL (.skipR (.seed (.lambdaAuto (.lambdaAuto (.lambdaAuto (.lambdaAuto .done))))))))

private def automaticAlias (left right : Bool) (port : Port scanExports branchFn.port := scanCaller)
    (observe : RecursiveCall.Numbered.CaptureCode machine := captureCode)
    (exactCheck : RecursiveCall.Numbered.ExactValueCheck machine := exactLambdas) :=
  admit instructionKeys actions Eq ordinaryOutputs 73 73 (number 1) (number 1)
    (scanModule left) (scanModule right) (autoPlan left right) (fn := branchFn) port 20 20
    observe (exactValue := exactCheck)

-- All λ rows use the same plan constructor, including the older unique
-- binding, the equal-body distinct capture, the exact duplicate and the caller.
#guard (automaticAlias false false).isSome
#guard (automaticAlias false false (.tail (.tail .head))).isSome
#guard (automaticAlias true true).isSome
#guard (automaticAlias false true).isNone
#guard (automaticAlias false false (exactCheck := fun _ _ => none)).isNone
#guard (automaticAlias false false (observe := .controlOnly machine)).isNone

private def asymmetricPlan (automatic : Bool) :
    Plan Op args args captureExports false (captureModule true).region (captureModule false true).region :=
  .skipL (.skipR (.skipL (.skipR (.seed (.lambda
    (if automatic then .lambdaAuto (.lambda .done) else .lambda (.lambda .done)))))))

private def asymmetricScan (automatic : Bool) :=
  admit instructionKeys actions Eq ordinaryOutputs 73 73 (number 1) (number 1)
    (captureModule true) (captureModule false true) (asymmetricPlan automatic) (fn := branchFn)
    (.tail (.tail .head)) 20 20 captureCode (exactValue := exactLambdas)

-- Padding the first right body makes both cross-side freshness checks pass
-- for the second pair. The second left value still duplicates its own first
-- row, so the automatic policy rejects it after the bilateral alias miss.
#guard (asymmetricScan false).isSome
#guard (asymmetricScan true).isNone

-- Base activation calls the λ from the outer capture of the later group.
private def aliasBase : RecursiveCall.Code Op (capturedWith branchFn.port) [] [[num]] [num] :=
  let flag := Origin.arg (.tail (.tail .head)) (past := [])
  let after := Origin.arg (.tail (.tail (.tail .head))) (past := [])
  .bind (RecursiveCall.simple (.apply branchFn) (.cons (.arg .head) (.cons flag (.cons after (.cons after .nil))))
      (fun i => i.elim0)) (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private abbrev mixedPast : List (Ports T) := [[global], [global], [branchFn.port], [branchFn.port], [branchFn.port]]
private abbrev mixedExports := [global, global, branchFn.port]
private abbrev mixedPort : Port mixedExports branchFn.port := .tail (.tail .head)

private def mixedSeed := selfGroup branchFn (.output (0 : Fin 2) .head : Origin args [[global], [global]] global)
  (branchBody baseL)

private def mixedGroup := selfGroup branchFn (.output (4 : Fin 5) .head : Origin args mixedPast branchFn.port)
  (branchBody aliasBase)

private def mixedModule :
    OmegaTerm Op args mixedExports (mixedPast ++ [[branchFn.port], [branchFn.port]]) :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.delta finishL) <| .bind (.phi mixedSeed) <|
    .bind (.lambda (sameBodyLambda (.output (1 : Fin 3) .head))) <|
    .bind (.lambda (sameBodyLambda (.output (1 : Fin 4) .head))) <|
    .bind (.phi mixedGroup) <| .bind (.lambda (wrapper (.output (5 : Fin 6) .head))) <|
    .ret (.cons (.output (0 : Fin 7) .head) (.cons (.output (1 : Fin 7) .head)
      (.cons (.output (6 : Fin 7) .head) .nil)))⟩

private def mixedPlan (checkAlias : Bool) :
    Plan Op args args mixedExports false mixedModule.region mixedModule.region :=
  .skipL (.skipR (.skipL (.skipR (.seed (.lambda
    (if checkAlias then .aliasFirst (.phi (.lambda .done)) else .skipL (.skipR (.phi (.lambda .done)))))))))

private def mixedAdmission (flag : Nat) (checkAlias : Bool := true) :=
  admit instructionKeys actions Eq ordinaryOutputs 73 73 (number flag) (number flag)
    mixedModule mixedModule (mixedPlan checkAlias) (fn := branchFn) mixedPort 20 20
    (exactValue := exactLambdas)

#guard (mixedAdmission 1).isSome
#guard (mixedAdmission 1 false).isNone
#guard (mixedAdmission 0).isNone

private def mixedLambdaRef : machine.Val branchFn.port :=
  .closure (.cons (globalValue 1 9) .nil) sameBody.toGraph

private def mixedMemberRef : machine.Val branchFn.port :=
  .member (.cons mixedLambdaRef .nil) mixedGroup.toGraph.definitions 0

-- The second initializer reads the first. Its allocated value reaches the
-- actual λ captured by the later φ. The λ alias itself has no link effect.
private theorem mixedLink : Executable.link actions 73 mixedModule.toGraph (number 1) 20 =
    .linked (.cons (globalValue 0 8) (.cons (globalValue 1 9)
      (.cons (wrapperRef mixedMemberRef) .nil))) 28 := by cbv

example : (match Executable.link actions 73 mixedModule.toGraph (number 0) 20 with
    | .undefined ⟨unitId, vertex, ⟨_, _, .finish, _, _, inputs⟩, store⟩ =>
      some (unitId, vertex, inputs, store)
    | _ => none) = some (73, 1, finishInputs 0 7 0, 23) := by cbv

-- The caller resumes after a recursive member activation calls the alias
-- and both recursion and the caller unwind through their saved suffixes.
example : Executable.run actions 80 73 mixedModule.toGraph (number 1) mixedPort (branchArgs 1) 20 =
    .ok (.returned (number 38) 45) := by
  unfold Executable.run Executable.start
  rw [mixedLink]
  cbv

private def profiledBody (right : Bool) (opcode : Op [num] [num]) :
    RecursiveCall.Code Op (branchEntryWith global) [] [[num], [num]] [num] :=
  if right then branchBodyWith baseR opcode else branchBodyWith baseL opcode

private def firstProfileGroup (right : Bool) :=
  selfGroup branchFn (.output (0 : Fin 2) .head : Origin args [[global], [global]] global)
    (profiledBody right .seed)

private def secondProfileGroup (right gain : Bool) :=
  selfGroup branchFn (.output (1 : Fin 3) .head : Origin args [[global], [global], [branchFn.port]] global)
    (profiledBody right (if gain then .gain else .seed))

private def profileGraph (right gain : Bool) :
    Omega Op args captureExports [[global], [global], [branchFn.port], [branchFn.port], [branchFn.port]] where
  region := {
    vertices := Fin.cases (.delta (seedDelta []).toGraph) <|
      Fin.cases (.delta finishL.toGraph) <|
      Fin.cases (.phi (firstProfileGroup right).toGraph) <|
      Fin.cases (.phi (secondProfileGroup right gain).toGraph) <|
      Fin.cases (.lambda (combined (past := [[global], [global], [branchFn.port], [branchFn.port]])
        (.output 2 .head) (.output 3 .head)).toGraph) (fun i => i.elim0)
    results := .cons (.output (2 : Fin 5) .head) (.cons (.output (3 : Fin 5) .head)
      (.cons (.output (4 : Fin 5) .head) .nil))
  }

private def profilePlan (gain : Bool) :
    GraphPlan (profileGraph false gain) (profileGraph true gain) :=
  .skipL (.skipR (.skipL (.skipR (.seed (.phi (.lambda .done))))))

private def profileAdmission (gain : Bool) (flag : Nat := 1) :=
  admitGraph instructionKeys actions Eq ordinaryOutputs 73 73 (number flag) (number flag)
    (profileGraph false gain) (profileGraph true gain) (profilePlan gain) (fn := branchFn)
    (.tail (.tail .head)) 20 20

-- Both groups have the same declared function and the same outer capture
-- type. Changing the outer suffix opcode separates their definitions.
#guard (profileAdmission true).isSome
#guard (profileAdmission false).isNone
#guard (profileAdmission true 0).isNone

private def firstProfileRef (right : Bool) : machine.Val branchFn.port :=
  .member (.cons (globalValue 0 8) .nil) (firstProfileGroup right).toGraph.definitions 0

private def secondProfileRef (right gain : Bool) : machine.Val branchFn.port :=
  .member (.cons (globalValue 1 9) .nil) (secondProfileGroup right gain).toGraph.definitions 0

example (right : Bool) : Executable.link actions 73 (profileGraph right true) (number 1) 20 =
    .linked (.cons (firstProfileRef right) (.cons (secondProfileRef right true)
      (.cons (.closure (.cons (firstProfileRef right) (.cons (secondProfileRef right true) .nil)) combinedBody.toGraph)
        .nil))) 28 := by
  cases right <;> cbv

-- Each export recurses, runs its own effectful suffix, and returns.
-- The caller captures both actual members and consumes both results.
example (right : Bool) :
    Executable.run actions 100 73 (profileGraph right true) (number 1) .head (branchArgs 1) 20 =
      .ok (.returned (number 30) 42) ∧
    Executable.run actions 100 73 (profileGraph right true) (number 1) (.tail .head) (branchArgs 1) 20 =
      .ok (.returned (number 45) 48) ∧
    Executable.run actions 100 73 (profileGraph right true) (number 1) (.tail (.tail .head)) (branchArgs 1) 20 =
      .ok (.returned (number 52) 65) := by
  cases right <;> exact ⟨by cbv, by cbv, by cbv⟩

-- The checker still rejects equal profiles even when different captured
-- payloads make the groups observationally distinct on this invocation.
example : Executable.run actions 100 73 (profileGraph false false) (number 1) (.tail .head)
    (branchArgs 1) 20 = .ok (.returned (number 31) 42) := by cbv

-- Undefined initialization is still a link error from the original table.
example : (match Executable.run actions 100 73 (profileGraph false true) (number 0)
    (.tail (.tail .head)) (branchArgs 1) 20 with
  | .error ⟨unitId, vertex, ⟨_, _, .finish, _, _, inputs⟩, store⟩ => some (unitId, vertex, inputs, store)
  | _ => none) = some (73, 1, finishInputs 0 7 0, 23) := by cbv

open RecursiveCall.Numbered (GroupProfile LabelCode memberProfile memberProfile_eq)

private def outerSeedCounts (profile : Option (GroupProfile Unit Unit instructionKeys.Key)) : Option (List Nat) :=
  letI : DecidableEq (LabelCode Unit Unit instructionKeys.Key) := inferInstance
  profile.map fun group => group.2.map fun labels => labels.count ([num], [num], .primitive (instructionKeys.encode (.primitive Op.seed)))

-- The runtime relation itself excludes a mixed dispatch, independently
-- of the differing captured payloads in the executable fixture.
example : ¬ValueRelated machine Eq (firstProfileRef false) (secondProfileRef true true) := by
  intro related
  have counts := congrArg outerSeedCounts (memberProfile_eq instructionKeys related)
  have first : outerSeedCounts (memberProfile instructionKeys (firstProfileRef false)) = some [1] := by cbv
  have second : outerSeedCounts (memberProfile instructionKeys (secondProfileRef true true)) = some [0] := by cbv
  rw [first, second] at counts
  cases counts

private abbrev twoMembers := [branchFn, branchFn]
private abbrev twoMemberPorts := memberPorts twoMembers

private def twoMemberGroup {past : List (Ports T)} (right : Bool) (capture : Origin args past global)
    (opcode : Op [num] [num]) (rewire : Bool := false) : PhiTerm Op args past twoMembers :=
  let body := profiledBody right opcode
  ⟨[global], .cons capture .nil,
    .cons ⟨[global, branchFn.port], .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), _, body⟩
      (.cons ⟨[global, branchFn.port], .cons (.arg .head)
        (.cons (if rewire then .arg (.tail .head) else .arg (.tail (.tail .head))) .nil), _, body⟩ .nil)⟩

private def originalAliasGroup (right : Bool) :=
  twoMemberGroup right (.output (0 : Fin 2) .head : Origin args [[global], [global]] global) .seed

private def otherAliasGroup (right : Bool) :=
  twoMemberGroup right (.output (1 : Fin 3) .head : Origin args [[global], [global], twoMemberPorts] global) .gain

private inductive GroupAliasExample where
  | first | second | changedCapture | rewiredSibling

private def aliasGroup (right : Bool) (choice : GroupAliasExample) :
    PhiTerm Op args [[global], [global], twoMemberPorts, twoMemberPorts] twoMembers :=
  match choice with
  | .first => twoMemberGroup right (.output (0 : Fin 4) .head) .seed
  | .second => twoMemberGroup right (.output (1 : Fin 4) .head) .gain
  | .changedCapture => twoMemberGroup right (.output (1 : Fin 4) .head) .seed
  | .rewiredSibling => twoMemberGroup right (.output (0 : Fin 4) .head) .seed true

private def groupAliasModule (right : Bool) (choice : GroupAliasExample) :
    OmegaTerm Op args captureExports [[global], [global], twoMemberPorts, twoMemberPorts,
      twoMemberPorts, [branchFn.port]] :=
  ⟨.bind (.delta (seedDelta [])) <| .bind (.delta finishL) <| .bind (.phi (originalAliasGroup right)) <|
    .bind (.phi (otherAliasGroup right)) <| .bind (.phi (aliasGroup right choice)) <|
    .bind (.lambda (wrapper (.output (4 : Fin 5) (.tail .head)))) <|
    .ret (.cons (.output (4 : Fin 6) .head) (.cons (.output (4 : Fin 6) (.tail .head))
      (.cons (.output (5 : Fin 6) .head) .nil)))⟩

private def groupAliasPlan (left right : GroupAliasExample) (prior : Nat) :
    Plan Op args args captureExports false (groupAliasModule false left).region (groupAliasModule true right).region :=
  .skipL (.skipR (.skipL (.skipR (.seed (.phi (.phiAlias prior (.lambda .done)))))))

private def groupAliasAdmission (left right : GroupAliasExample) (prior : Nat)
    (port : Port captureExports branchFn.port := .tail (.tail .head))
    (exactValue : RecursiveCall.Numbered.ExactValueCheck machine := exactFirstOrder) :=
  admit instructionKeys actions Eq ordinaryOutputs 73 73 (number 1) (number 1)
    (groupAliasModule false left) (groupAliasModule true right) (groupAliasPlan left right prior)
    (fn := branchFn) port 20 20 (exactValue := exactValue)

#guard (groupAliasAdmission .first .first 1 .head).isSome
#guard (groupAliasAdmission .first .first 1 (.tail .head)).isSome
#guard (groupAliasAdmission .first .first 1).isSome
#guard (groupAliasAdmission .second .second 0).isSome

-- A match on one side or matches at different rows cannot certify a paired alias.
#guard (groupAliasAdmission .first .changedCapture 1).isNone
#guard (groupAliasAdmission .changedCapture .changedCapture 1).isNone
#guard (groupAliasAdmission .first .second 1).isNone
#guard (groupAliasAdmission .first .second 0).isNone
#guard (groupAliasAdmission .rewiredSibling .rewiredSibling 1 .head).isNone
#guard (groupAliasAdmission .first .first 1 (exactValue := fun _ _ => none)).isNone

private def originalAliasRef (right : Bool) (slot : Fin twoMembers.length) : machine.Val twoMembers[slot].port :=
  .member (.cons (globalValue 0 8) .nil) (originalAliasGroup right).toGraph.definitions slot

-- Linking either alias slot produces the same value the earlier group
-- supplied at that slot. The later caller captures the second alias.
example (right : Bool) : Executable.link actions 73 (groupAliasModule right .first).toGraph (number 1) 20 =
    .linked (.cons (originalAliasRef right 0) (.cons (originalAliasRef right 1)
      (.cons (wrapperRef (originalAliasRef right 1)) .nil))) 28 := by
  cases right <;> cbv

example (right : Bool) :
    Executable.run actions 80 73 (groupAliasModule right .first).toGraph (number 1) .head (branchArgs 1) 20 =
      .ok (.returned (number 30) 42) ∧
    Executable.run actions 80 73 (groupAliasModule right .first).toGraph (number 1) (.tail (.tail .head)) (branchArgs 1) 20 =
      .ok (.returned (number 37) 45) := by
  cases right <;> exact ⟨by cbv, by cbv⟩

private abbrev seedRow {past : List (Ports T)} : NestedTheta.Node (Instruction Op) [global, num] past [num] :=
  RecursiveCall.simple (.primitive Op.seed) (.cons (.arg (.tail .head)) .nil) (fun i => i.elim0)

private abbrev finishRow {past : List (Ports T)} : NestedTheta.Node (Instruction Op) [global, num] past [num] :=
  RecursiveCall.simple (.primitive Op.finish)
    (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) (fun i => i.elim0)

private def seedThenFinish : RecursiveCall.Code Op [global, num] [] [[num], [num]] [] :=
  .bind seedRow (fun i => i.elim0) (.bind finishRow (fun i => i.elim0) (.ret .nil))

private def finishThenSeed : RecursiveCall.Code Op [global, num] [] [[num], [num]] [] :=
  .bind finishRow (fun i => i.elim0) (.bind seedRow (fun i => i.elim0) (.ret .nil))

-- The graph swap preserves both labels and their independent operands.
-- It moves the state change across a potentially undefined action.
private theorem effectSwapIso :
    NestedTheta.Graph.Isomorphic (Instruction Op) seedThenFinish.toGraph finishThenSeed.toGraph := by
  refine .intro rfl rfl (Equiv.swap (0 : Fin 2) 1) ?_ ?_ rfl ?_
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases rfl (Fin.cases rfl (fun i => i.elim0))
  · exact Fin.cases (fun i => i.elim0) (Fin.cases (fun i => i.elim0) (fun i => i.elim0))

example : RecursiveCall.Numbered.outerProfile instructionKeys seedThenFinish.toGraph =
    RecursiveCall.Numbered.outerProfile instructionKeys finishThenSeed.toGraph :=
  RecursiveCall.Numbered.outerProfile_eq instructionKeys effectSwapIso

example : (RecursiveCall.Numbered.infer instructionKeys
    seedThenFinish.toGraph finishThenSeed.toGraph).isSome = false := by cbv

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Tests
