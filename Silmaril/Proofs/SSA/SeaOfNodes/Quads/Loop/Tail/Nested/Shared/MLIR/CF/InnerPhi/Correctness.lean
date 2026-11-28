module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.MLIR.Thms
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Proofs

open SeaOfNodes.Diamond (Ty ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model evalOp opcode opcode_eval)
open SeaOfNodes.MLIR.Lowering (Scope encodeValues lowerCode lowerCode_eval operands valueBits)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Edge)
open Silmaril.MLIR.Pure (Code Operands)
open Outer.MLIR.CF.Phi (atTarget terminal terminalEnv)
open Outer.MLIR.CF.Phi.Readback (successor)
open Diamond.MLIR.CF (Label Widths blockNames blockNames_agree fullJump lowerBlock lowerBlockWith lowerTerminator
  lowerTerminatorWith lowerDestinationWith runBlock_eq_of_frames source_site_eval siteFrame)
open Join (Block Opcode)
open Join.Finite (Plan Stage)
open RVSDG (Locals Tuple Wires extend)
open RVSDG.NestedTheta (Graph Term)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase_eval)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Prefix.Routes src entry)
variable (input old : Bank (regs := regs) model)

private def sourceSlot (slot : Fin 2) : Tail.Terminator regs out size → Option (Destination regs out size)
  | .transfer dest => if slot = 0 then some dest else none
  | .branch _ yes no => some (if slot = 0 then yes else no)

private theorem last_slot {target site : Fin size} (path : Chain.Segment src target site) (caller : Fin size)
    (slot : Fin 2) (direct : sourceSlot slot (src caller).terminator = some (.jump site)) :
    sourceSlot (if path.blocks.isEmpty then slot else 0)
        (src (path.predecessor caller)).terminator = some (.jump target) := by
  induction path generalizing caller slot with
  | empty => exact direct
  | jump site edge rest ih =>
    have arrives := ih site 0 (by rw [edge]; rfl)
    simpa [Chain.Segment.blocks, Chain.Segment.predecessor] using arrives

private theorem admitted_slot (taken : Bool) :
    sourceSlot (p.innerEdgeOccurrence taken).2 (src (p.innerEdgeOccurrence taken).1).terminator =
      some (.jump p.meet) := by
  cases taken
  · have step := last_slot p.innerFalse p.inner 1 (by rw [p.innerEdge]; rfl)
    simpa [Prefix.Routes.innerEdgeOccurrence, Bool.cond_eq_ite] using step
  · have step := last_slot p.innerTrue p.inner 0 (by rw [p.innerEdge]; rfl)
    simpa [Prefix.Routes.innerEdgeOccurrence] using step

private theorem last_bank {target site : Fin size} (path : Chain.Segment src target site)
    (caller : Fin size) (before current : Bank (regs := regs) model)
    (updated : (src caller).body.eval model before = current) :
    (src (path.predecessor caller)).body.eval model (path.predecessorBank model before current) =
      path.quads.eval model current := by
  induction path generalizing caller before current with
  | empty => exact updated
  | jump site edge rest ih =>
    exact (ih site current ((src site).body.eval model current) rfl).trans List.foldl_append.symm

private theorem prefix_packet (taken : Bool) :
    (src (p.innerEdgeOccurrence taken).1).body.eval model (beforePredecessor p taken old) =
      p.prefixBank model old (occurrence taken) := by
  rw [Prefix.prefix_bank]
  cases taken
  · rw [show (p.innerEdgeOccurrence false).1 = p.innerFalse.predecessor p.inner from rfl]
    exact (last_bank p.innerFalse p.inner (headerBank p old) (splitBank p old) rfl).trans
      (by simp only [occurrence, Bool.false_eq_true, ite_false, Prefix.Routes.prefixQuads, Block.eval,
        List.foldl_append, splitBank, headerBank])
  · rw [show (p.innerEdgeOccurrence true).1 = p.innerTrue.predecessor p.inner from rfl]
    exact (last_bank p.innerTrue p.inner (headerBank p old) (splitBank p old) rfl).trans
      (by simp only [occurrence, ite_true, Prefix.Routes.prefixQuads, Block.eval, List.foldl_append, splitBank, headerBank])

private theorem lowered_slot {past Γ} (scope : SeaOfNodes.MLIR.Lowering.Scope (dataPorts regs) past Γ)
    (versions : Wires (dataPorts regs) past (dataPorts regs))
    (term : Tail.Terminator regs out size) (slot : Fin 2) (target : Fin size)
    (valid : sourceSlot slot term = some (.jump target)) :
    (successor slot (lowerTerminator scope versions term)).bind (atTarget target) = some (operands scope versions) := by
  cases term with
  | transfer dest =>
    by_cases zero : slot = 0
    · simp only [sourceSlot, ite_eq_left zero, Option.some.injEq] at valid
      subst dest
      simp [lowerTerminator, lowerTerminatorWith, lowerDestinationWith, fullJump, successor, atTarget, zero]
    · simp [sourceSlot, zero] at valid
  | branch _ yes no =>
    by_cases zero : slot = 0
    · simp only [sourceSlot, ite_eq_left zero, Option.some.injEq] at valid
      subst yes
      simp [lowerTerminator, lowerTerminatorWith, lowerDestinationWith, fullJump, successor, atTarget, zero]
    · simp only [sourceSlot, ite_eq_right zero, Option.some.injEq] at valid
      subst no
      simp [lowerTerminator, lowerTerminatorWith, lowerDestinationWith, fullJump, successor, atTarget, zero]

private theorem eval_terminal {Γ : List Width} {Term : List Width → Type} {A : Type}
    (code : Silmaril.MLIR.Pure.Code TargetOp Term Γ) (env : Env Γ) (finish : ∀ {γ}, Term γ → Env γ → A) :
    code.eval evalOp finish env = finish (terminal code).2 (terminalEnv code env) := by
  induction code with
  | terminator => rfl
  | letOp _ _ _ ih => exact ih _

theorem incoming_packet (taken : Bool) :
    (incoming p taken).map (fun operands => operands.eval (arrivalEnv p taken input old)) =
      some (encodeValues (p.prefixBank model old (occurrence taken))) := by
  let i := (p.innerEdgeOccurrence taken).1
  let slot := (p.innerEdgeOccurrence taken).2
  let before := beforePredecessor p taken old
  let captures := encodeValues input
  let finish {Γ : List Width} (term : Silmaril.MLIR.CF.Terminator (Label regs out size)
      [SeaOfNodes.MLIR.Lowering.valueWidth out] Γ) (env : Env Γ) :=
    ((successor slot term).bind (atTarget p.meet)).map fun operands => operands.eval env
  have evaluated :
      ((cfg p).block (.site i)).eval evalOp finish ((encodeValues before).append captures) =
        some (encodeValues ((src i).body.eval model before)) := by
    change (lowerBlock (src i) ⟨blockNames (Widths regs) regs, PUnit.unit⟩).eval evalOp finish _ = _
    unfold lowerBlock lowerBlockWith
    let compiled := CFG.compileBlock (src i).body (initial regs)
    have agrees : SeaOfNodes.MLIR.Lowering.NamesAgree ((encodeValues before).append captures)
        (blockNames (Widths regs) regs) before := blockNames_agree captures before
    refine lowerCode_eval opcode evalOp model.run opcode_eval compiled.flow _ _ before PUnit.unit
      ⟨agrees, trivial⟩ _ finish _ ?_
    intro Γ scope env ok
    change ((successor slot (lowerTerminator scope compiled.outgoing (src i).terminator)).bind
      (atTarget p.meet)).map (fun operands => operands.eval env) = _
    rw [lowered_slot scope compiled.outgoing _ _ _ (admitted_slot p taken)]
    simp only [Option.map_some, Option.some.injEq]
    rw [ok.operands_eval]
    have bank := CFG.compileBlock_read (past := []) (src i).body model before PUnit.unit (initial regs)
    rw [Quads.read_initial model] at bank
    rw [bank]
  rw [prefix_packet p old taken] at evaluated
  rw [eval_terminal] at evaluated
  exact evaluated

private def zeroBank : (types : List (ValueSort Width)) → Bank (regs := types) model
  | [] => .nil
  | .predicate :: rest => .cons ⟨false⟩ (zeroBank rest)
  | .data w :: rest => .cons (BitVec.ofNat w.val 0) (zeroBank rest)

theorem rows_exist : ∃ rows, readRows p = some rows := by
  have present (taken : Bool) : (incoming p taken).isSome = true := by
    have agreement := incoming_packet p (zeroBank regs) (zeroBank regs) taken
    cases seen : incoming p taken
    · rw [seen] at agreement
      cases agreement
    · rfl
  refine ⟨_, Option.eq_some_of_isSome ?_⟩
  rw [readRows, dite_eq_left ⟨present true, present false⟩]
  rfl

theorem rebuild_slot (rows : Rows p) (taken : Bool) :
    successor (p.innerEdgeOccurrence taken).2 (terminal (predecessor p taken)).2 =
      some ⟨.site p.meet, rows.operands taken⟩ := by
  have checked := rows.checked taken
  unfold incoming at checked
  generalize successor (p.innerEdgeOccurrence taken).2 (terminal (predecessor p taken)).2 = edge at *
  cases edge with
  | none => cases checked
  | some e =>
    rcases e with ⟨label, ops⟩
    cases label with
    | exit => cases checked
    | site id =>
      simp only [Option.bind_some, atTarget] at checked
      split at checked
      · rename_i same
        subst id
        cases Option.some.inj checked
        rfl
      · cases checked

private theorem from_site (fuel : Nat) (id : Fin size) (bank : Bank (regs := regs) model) :
    (cfg p).runFrom evalOp (fuel + 1) (encodeValues input) (siteFrame id bank) =
      (src.runFrom model fuel id bank).map (fun value => Env.cons (valueBits value) .nil) :=
  runBlock_eq_of_frames (cfg p) input siteFrame .exit
    (fun id incoming => source_site_eval input incoming id) rfl fuel id bank _ _ (source_site_eval input bank id)

theorem from_header (fuel : Nat) (entered : ((headerBank p old).get p.outerTest).down = true) :
    let selected := occurrence (side p old)
    (cfg p).runFrom evalOp (fuel + p.prefixVisits selected + 1) (encodeValues input) (siteFrame p.header old) =
      (cfg p).runFrom evalOp (fuel + 1) (encodeValues input) (siteFrame p.meet (p.prefixBank model old selected)) := by
  dsimp only
  rw [from_site p input, from_site p input]
  have selected : p.toControl.selected model old = occurrence (side p old) := by
    change (if ((headerBank p old).get p.outerTest).down then occurrence (side p old) else .outerFalse) = _
    rw [ite_eq_left entered]
  have reaches := Prefix.run_prefix p model old fuel
  dsimp only at reaches
  rw [selected] at reaches
  have target : p.prefixTarget (occurrence (side p old)) = p.meet := by
    cases side p old <;> rfl
  rw [target] at reaches
  rw [reaches]

theorem after_inner_run {results : List (SeaOfNodes.Diamond.Ty Width)} {suffix : List (List (SeaOfNodes.Diamond.Ty Width))}
    (finish : Wires (dataPorts regs) (gammaScope p) (dataPorts regs) →
      Term (Opcode Op) (dataPorts regs) (gammaScope p) suffix results)
    (header : Bank (regs := regs) model) (fuel : Nat)
    (observe : Bank (regs := regs) model → Option (Tuple (SeaOfNodes.Diamond.Val model.value) results))
    (agrees : ∀ wires locals, (finish wires).eval (Join.model model) fuel header locals =
      observe (wires.read header locals)) :
    (afterInner p finish).run (Join.model model) fuel header =
      observe ((Prefix.innerPlan p).eval model ((src p.inner).body.eval model header)) := by
  unfold afterInner Term.run
  erw [thenBase_eval (observe := fun bank => observe ((Prefix.innerPlan p).eval model bank))]
  · erw [Block.lowerFrom_eval, read_initial]
    rfl
  · intro wires locals
    erw [thenBase_eval (observe := observe), Plan.lowerFrom_eval]
    exact agrees

theorem gamma_run (fuel : Nat) :
    (gamma p).run (Join.model model) fuel (headerBank p old) =
      some (p.prefixBank model old (occurrence (side p old))) := by
  rw [gamma, ← Graph.run_toTerm, Term.toTerm_toGraph, after_inner_run p _ _ _ some (fun _ _ => rfl), Prefix.prefix_bank]
  let mid := splitBank p old
  change some ((Prefix.innerPlan p).eval model mid) =
    some ((p.prefixQuads (occurrence ((mid.get p.innerTest).down))).eval model old)
  by_cases yes : (mid.get p.innerTest).down = true
  · have route : occurrence ((mid.get p.innerTest).down) = .innerTrue := by simp [occurrence, yes]
    rw [route]
    simp only [Prefix.innerPlan, Plan.eval, List.foldl_cons, List.foldl_nil,
      Stage.eval, Stage.table, Join.Choice.eval, ite_eq_left yes]
    simp only [Prefix.Routes.prefixQuads, Block.eval, List.foldl_append, mid, splitBank, headerBank]
    rfl
  · have route : occurrence ((mid.get p.innerTest).down) = .innerFalse := by simp [occurrence, yes]
    rw [route]
    simp only [Prefix.innerPlan, Plan.eval, List.foldl_cons, List.foldl_nil,
      Stage.eval, Stage.table, Join.Choice.eval, ite_eq_right yes]
    simp only [Prefix.Routes.prefixQuads, Block.eval, List.foldl_append, mid, splitBank, headerBank]
    rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Proofs
