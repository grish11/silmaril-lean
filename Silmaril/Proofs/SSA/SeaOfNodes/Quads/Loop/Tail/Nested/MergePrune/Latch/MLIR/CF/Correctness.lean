module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.MLIR.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Proofs

open SeaOfNodes.Diamond (Dataflow Val ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model opcode opcode_eval evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Cfg Edge Frame)
open Diamond.MLIR.CF (JumpAgrees destinationFrameWith returnFrame entryNames_agree blockNames_agree
  block_eval_with runBlock_eq_of_frames_with)
open Diamond.MLIR.CF.Pruned (projectedBlock_eval)
open Diamond.Prune (HeaderProjection)
open RVSDG (Tuple Wires Locals extend)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch)

private theorem jump_agrees :
    JumpAgrees (jump (carry := carry) (merge := merge) (atLatch := atLatch) p)
      (siteFrame p) := by
  intro _ _ _ scope env input locals ok versions id
  by_cases cut : id = p.latch
  · simp only [jump, siteFrame, ite_eq_left cut, latchFrame]
    have bank := ok.operands_eval (ins := atLatch.kept) (atLatch.project versions)
    rw [atLatch.project_read model input locals versions] at bank
    exact congrArg (fun bits => Frame.mk Label.latch bits) bank
  · simp only [jump, siteFrame, ite_eq_right cut]
    exact congrArg (liftFrame (atLatch := atLatch) p) (MergePrune.MLIR.CF.jump_agrees p carry merge ok versions id)

private theorem merge_ne_header : p.join ≠ p.header := by
  intro same
  exact (List.nodup_cons.mp (List.nodup_cons.mp p.distinct).2).1 (by simp [← same])

private theorem latch_ne_header : p.latch ≠ p.header := by
  intro same
  exact (List.nodup_cons.mp (List.nodup_cons.mp p.distinct).2).1 (by simp [← same])

private theorem latch_ne_merge : p.latch ≠ p.join := by
  intro same
  have distinct := (List.nodup_append.mp p.distinct).2.1
  exact (List.nodup_cons.mp distinct).1 (by simp [same])

private theorem at_header (old : Bank (regs := regs) model) :
    siteFrame (merge := merge) (atLatch := atLatch) p p.header old = headerFrame p (carry.project old) := by
  unfold siteFrame
  rw [ite_eq_right (latch_ne_header p).symm, MergePrune.MLIR.CF.siteFrame, dite_eq_left rfl]
  rfl

private theorem at_merge (old : Bank (regs := regs) model) :
    siteFrame (carry := carry) (atLatch := atLatch) p p.join old = mergeFrame p (merge.project old) := by
  unfold siteFrame
  rw [ite_eq_right (latch_ne_merge p).symm, MergePrune.MLIR.CF.siteFrame,
    dite_eq_right (merge_ne_header p), dite_eq_left rfl]
  rfl

private theorem emit_transfer {body : Join.Block Op regs} {mask : Mask regs}
    {outputs : List (SeaOfNodes.Diamond.Ty Width)}
    {wires : Wires (dataPorts regs) (extend [] body.producers) outputs}
    (transfer : Split.Transfer body mask wires) (input : Bank (regs := mask.kept) model)
    (captures : Bank (regs := regs) model)
    (term : ∀ {Δ}, Scope (dataPorts mask.kept) (extend [] body.producers) Δ →
      Silmaril.MLIR.CF.Terminator (Label p.header p.join p.latch carry merge atLatch out) [valueWidth out] Δ)
    (observe : Tuple (Val Word) outputs → Frame (Label p.header p.join p.latch carry merge atLatch out))
    (agrees : ∀ {Δ} (scope : Scope (dataPorts mask.kept) (extend [] body.producers) Δ)
        (env : Env Δ), scope.Agrees env input (transfer.flow.eval model input PUnit.unit) →
      (term scope).eval env = .inl (observe (transfer.eval model input))) :
    (lowerCode opcode transfer.flow ⟨Diamond.MLIR.CF.blockNames _ mask.kept, PUnit.unit⟩ term).eval
        evalOp (fun term env => term.eval env) ((encodeValues input).append (encodeValues captures)) =
      .inl (observe (transfer.eval model input)) :=
  lowerCode_eval opcode evalOp model.run opcode_eval transfer.flow _ _ input (past := []) PUnit.unit
    ⟨blockNames_agree (encodeValues captures) input, trivial⟩ term (fun term env => term.eval env) _ agrees

/-- Evaluate the actual narrowed merge block and read its outgoing latch frame. -/
theorem merge_frame (input old : Bank (regs := regs) model) :
    ((lower p projected checked).block (.base .merge)).eval evalOp (fun term env => term.eval env)
        ((encodeValues (merge.project old)).append (encodeValues input)) =
      .inl (latchFrame p (atLatch.project ((src p.join).body.eval model old))) := by
  refine (emit_transfer p checked.mergeTransfer (merge.project old) input
    (fun scope => .br ⟨.latch, operands scope checked.mergeTransfer.outgoing⟩)
    (latchFrame p) ?_).trans ?_
  · intro _ _ _ ok
    exact congrArg (fun args => Sum.inl (Frame.mk Label.latch args))
      (ok.operands_eval (ins := atLatch.kept) checked.mergeTransfer.outgoing)
  · exact congrArg (fun bank => Sum.inl (latchFrame (carry := carry) (merge := merge) p bank))
      (Split.Checked.merge_agrees checked model old)

private theorem latchTerminator_eval {Γ : List Width} {args : List (SeaOfNodes.Diamond.Ty Width)}
    {past : List (List (SeaOfNodes.Diamond.Ty Width))} {scope : Scope args past Γ} {env : Env Γ}
    {inputs : Tuple (Val Word) args} {locals : Locals (Val Word) past}
    (ok : scope.Agrees env inputs locals) (packet : Wires args past (packetPorts out carry)) :
    (latchTerminator (merge := merge) (atLatch := atLatch) p scope packet).eval env =
      .inl (packetFrame p (packet.read inputs locals)) := by
  cases packet with
  | cons test rest =>
    cases rest with
    | cons returned feedback =>
      have predicate := ok.resolve test
      have returnedWord := ok.resolve returned
      have feedbackBank := ok.operands_eval (ins := carry.kept) feedback
      change _ = valueBits (s := .predicate) (SeaOfNodes.Diamond.read model test inputs locals) at predicate
      change _ = valueBits (s := out) (SeaOfNodes.Diamond.read model returned inputs locals) at returnedWord
      have bit (b : Bool) : (BitVec.ofBool b).getLsbD 0 = b := by cases b <;> rfl
      have guard := (congrArg (fun bits : BitVec 1 => bits.getLsbD 0) predicate).trans (bit _)
      change Sum.inl (if (env.get (scope.resolveValue test)).getLsbD 0 then
          Frame.mk (Label.base (atLatch := atLatch) (merge := merge) (header := p.header)
            (join := p.join) (latch := p.latch) (out := out) .header) ((operands scope feedback).eval env)
        else Frame.mk (Label.base .exit) (.cons (env.get (scope.resolveValue returned)) .nil)) = _
      erw [guard, feedbackBank, returnedWord]
      rfl

theorem latchCode_eval {sigs : List (List (SeaOfNodes.Diamond.Ty Width))}
    (flow : Dataflow Op (dataPorts atLatch.kept) [] sigs)
    (packet : Wires (dataPorts atLatch.kept) (extend [] sigs) (packetPorts out carry))
    (input : Bank (regs := regs) model) (old : Bank (regs := atLatch.kept) model) :
    (latchCode (carry := carry) (merge := merge) (atLatch := atLatch) p flow packet).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl (packetFrame p (packet.read old (flow.eval model old PUnit.unit))) :=
  lowerCode_eval opcode evalOp model.run opcode_eval flow _ _ old (past := []) PUnit.unit
    ⟨blockNames_agree (encodeValues input) old, trivial⟩
    (fun scope => latchTerminator p scope packet) (fun term env => term.eval env) _
    (fun _ _ ok => latchTerminator_eval p ok packet)

/-- Execute the original tested latch with the certified smaller input. -/
theorem latch_frame (input old : Bank (regs := regs) model) :
    ((lower p projected checked).block .latch).eval evalOp (fun term env => term.eval env)
        ((encodeValues (atLatch.project old)).append (encodeValues input)) =
      let next := (src p.latch).body.eval model old
      .inl (if (next.get p.again).down then headerFrame p (carry.project next) else exitFrame p (next.get p.result)) := by
  exact (latchCode_eval (merge := merge) p checked.latchTransfer.flow checked.latchTransfer.outgoing
    input (atLatch.project old)).trans
    (congrArg (fun packet => Sum.inl (packetFrame (merge := merge) (atLatch := atLatch) p packet))
      (Split.Checked.latch_agrees checked model old))

theorem site_frame (input old : Bank (regs := regs) model) (id : Fin size) :
    let current := siteFrame (carry := carry) (merge := merge) (atLatch := atLatch) p id old
    let next := (src id).body.eval model old
    ((lower p projected checked).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append (encodeValues input)) =
      .inl (destinationFrameWith (siteFrame p) (exitFrame p) next ((src id).terminator.select model next)) := by
  dsimp only
  by_cases latch : id = p.latch
  · subst id
    rw [siteFrame, ite_eq_left rfl]
    refine (latch_frame p projected checked input old).trans ?_
    simp only [p.latchEdge, Tail.Terminator.select]
    by_cases test : (((src p.latch).body.eval model old).get p.again).down = true
    · simp [test, destinationFrameWith, at_header p]
    · simp [test, destinationFrameWith]
  · by_cases header : id = p.header
    · subst id
      rw [at_header p]
      exact projectedBlock_eval (jump_agrees p) (.base .exit) (src p.header) projected (encodeValues input) old
    · by_cases mergeSite : id = p.join
      · subst id
        rw [at_merge p, p.joinEdge]
        simp only [Tail.Terminator.select, destinationFrameWith]
        rw [siteFrame, ite_eq_left rfl]
        exact merge_frame p projected checked input old
      · have frame : siteFrame (carry := carry) (merge := merge) (atLatch := atLatch) p id old =
          ⟨.base (.site id header mergeSite), encodeValues old⟩ := by
          unfold siteFrame
          rw [ite_eq_right latch, MergePrune.MLIR.CF.siteFrame, dite_eq_right header, dite_eq_right mergeSite]
          rfl
        rw [frame]
        exact block_eval_with (jump_agrees p) (src id) _ _ old (blockNames_agree (encodeValues input) old)

private theorem segment_edge {target site : Fin size} (path : Chain.Segment src target site)
    (caller : Fin size) (old : Bank (regs := regs) model)
    (taken : (src caller).terminator.select model ((src caller).body.eval model old) = .jump site) :
    let pred := path.predecessor caller
    let next := (src pred).body.eval model
      (segmentPredecessorBank path old ((src caller).body.eval model old))
    (src pred).terminator.select model next = .jump target ∧
      next = path.quads.eval model ((src caller).body.eval model old) := by
  induction path generalizing caller old with
  | empty => exact ⟨taken, rfl⟩
  | jump site edge rest ih =>
    have next := ih site ((src caller).body.eval model old) (by rw [edge]; rfl)
    exact ⟨next.1, next.2.trans List.foldl_append.symm⟩

private theorem selected_edge (old : Bank (regs := regs) model) :
    let occurrence := p.selected model old
    let pred := p.predecessor occurrence
    let next := (src pred).body.eval model (predecessorBank p old occurrence)
    (src pred).terminator.select model next = .jump p.join ∧ next = p.mergeBank model old occurrence := by
  let outer := (src p.header).body.eval model old
  let inner := (src p.inner).body.eval model outer
  have select : p.selected model old =
      if (outer.get p.outerTest).down then
        if (inner.get p.innerTest).down then .innerTrue else .innerFalse
      else .outerFalse := rfl
  dsimp only
  rw [select]
  by_cases outerTrue : (outer.get p.outerTest).down = true
  · rw [ite_eq_left outerTrue]
    by_cases innerTrue : (inner.get p.innerTest).down = true
    · rw [ite_eq_left innerTrue]
      have edge : (src p.inner).terminator.select model inner = .jump p.onInnerTrue := by
        simp only [p.innerEdge, Tail.Terminator.select, ite_eq_left innerTrue]
      obtain ⟨route, bank⟩ := segment_edge p.innerTrue p.inner outer edge
      exact ⟨route, bank.trans ((p.merge_bank model old .innerTrue).trans (by
        change _ = p.innerTrue.quads.eval model inner
        simp only [Program.pathQuads, Program.arm, Join.Block.eval, inner, outer, List.foldl_append]; rfl)).symm⟩
    · rw [ite_eq_right innerTrue]
      have edge : (src p.inner).terminator.select model inner = .jump p.onInnerFalse := by
        simp only [p.innerEdge, Tail.Terminator.select, ite_eq_right innerTrue]
      obtain ⟨route, bank⟩ := segment_edge p.innerFalse p.inner outer edge
      exact ⟨route, bank.trans ((p.merge_bank model old .innerFalse).trans (by
        change _ = p.innerFalse.quads.eval model inner
        simp only [Program.pathQuads, Program.arm, Join.Block.eval, inner, outer, List.foldl_append]; rfl)).symm⟩
  · rw [ite_eq_right outerTrue]
    have edge : (src p.header).terminator.select model outer = .jump p.onOuterFalse := by
      simp only [p.outerEdge, Tail.Terminator.select, ite_eq_right outerTrue]
    obtain ⟨route, bank⟩ := segment_edge p.outerFalse p.header old edge
    exact ⟨route, bank.trans ((p.merge_bank model old .outerFalse).trans (by
      change _ = p.outerFalse.quads.eval model outer
      simp only [Program.pathQuads, Program.arm, Join.Block.eval, outer, List.foldl_append]; rfl)).symm⟩

theorem selected_predecessor_frame (input old : Bank (regs := regs) model) :
    let occurrence := p.selected model old
    let frame := siteFrame p (p.predecessor occurrence) (predecessorBank p old occurrence)
    ((lower p projected checked).block frame.label).eval evalOp (fun term env => term.eval env)
      (frame.args.append (encodeValues input)) =
      .inl (mergeFrame p (incoming p merge model old occurrence)) := by
  have edge := selected_edge p old
  dsimp only at edge ⊢
  rw [site_frame p projected checked, edge.1, destinationFrameWith, edge.2, at_merge]
  rfl

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p projected checked).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun word => Env.cons (valueBits word) .nil) :=
  runBlock_eq_of_frames_with (lower p projected checked) (encodeValues input) (siteFrame p) (.base .exit)
    (fun id old => site_frame p projected checked input old id) rfl fuel entry input _ _
    (block_eval_with (jump_agrees p) (src entry) _ _ _ (entryNames_agree input))

/-- Reuse the source visit proof when the replacement latch supplies the
same actual successor frame for every projected source bank. -/
theorem withLatch_lower_run
    (block : LatchBlock (carry := carry) (merge := merge) (atLatch := atLatch) p)
    (input : Bank (regs := regs) model)
    (agrees : ∀ old : Bank (regs := regs) model,
      block.eval evalOp (fun term env => term.eval env)
          ((encodeValues (atLatch.project old)).append (encodeValues input)) =
        ((lower p projected checked).block .latch).eval evalOp (fun term env => term.eval env)
          ((encodeValues (atLatch.project old)).append (encodeValues input)))
    (fuel : Nat) :
    (withLatch p (lower p projected checked) block).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun word => Env.cons (valueBits word) .nil) := by
  let cfg := withLatch p (lower p projected checked) block
  have frameEq (id : Fin size) (old : Bank (regs := regs) model) :
      let current := siteFrame (carry := carry) (merge := merge) (atLatch := atLatch) p id old
      (cfg.block current.label).eval evalOp (fun term env => term.eval env)
          (current.args.append (encodeValues input)) =
        ((lower p projected checked).block current.label).eval evalOp (fun term env => term.eval env)
          (current.args.append (encodeValues input)) := by
    dsimp only
    by_cases same : id = p.latch
    · subst id
      rw [siteFrame, ite_eq_left rfl]
      exact agrees old
    · rw [siteFrame, ite_eq_right same]
      rfl
  exact runBlock_eq_of_frames_with cfg (encodeValues input) (siteFrame p) (.base .exit)
    (fun id old => (frameEq id old).trans (site_frame p projected checked input old id))
    rfl fuel entry input _ _
    (block_eval_with (jump_agrees p) (src entry) _ _ _ (entryNames_agree input))

theorem source_returns_iff (input : Bank (regs := regs) model) (output : Env [valueWidth out]) :
    (∃ fuel, (lower p projected checked).run evalOp fuel (encodeValues input) = some output) ↔
      ∃ fuel, (src.runFrom model fuel entry input).map (fun word => Env.cons (valueBits word) .nil) = some output := by
  constructor
  · rintro ⟨_ | fuel, returned⟩
    · cases returned
    · exact ⟨fuel, (lower_run p projected checked fuel input).symm.trans returned⟩
  · rintro ⟨fuel, returned⟩
    exact ⟨fuel + 1, (lower_run p projected checked fuel input).trans returned⟩

theorem source_diverges_iff (input : Bank (regs := regs) model) :
    (lower p projected checked).Diverges evalOp (encodeValues input) ↔
      ∀ fuel, src.runFrom model fuel entry input = none := by
  constructor
  · intro exhausted fuel
    exact Option.map_eq_none_iff.mp
      ((lower_run p projected checked fuel input).symm.trans (exhausted (fuel + 1)))
  · intro exhausted fuel
    cases fuel with
    | zero => rfl
    | succ fuel => rw [lower_run, exhausted]; rfl

private theorem from_run (fuel : Nat) (input old : Bank (regs := regs) model) (id : Fin size) :
    (lower p projected checked).runFrom evalOp (fuel + 1) (encodeValues input) (siteFrame p id old) =
      (src.runFrom model fuel id old).map (fun word => Env.cons (valueBits word) .nil) :=
  runBlock_eq_of_frames_with (lower p projected checked) (encodeValues input) (siteFrame p) (.base .exit)
    (fun id old => site_frame p projected checked input old id) rfl fuel id old _ _
    (site_frame p projected checked input old id)

theorem from_header_eq_merge (fuel : Nat) (input old : Bank (regs := regs) model) :
    let occurrence := p.selected model old
    (lower p projected checked).runFrom evalOp (fuel + p.mergeVisits occurrence + 1) (encodeValues input)
        (siteFrame p p.header old) =
      (lower p projected checked).runFrom evalOp (fuel + 1) (encodeValues input)
        (mergeFrame p (incoming p merge model old occurrence)) := by
  dsimp only
  unfold incoming
  rw [← at_merge p (p.mergeBank model old (p.selected model old)), from_run, from_run, p.run_to_merge]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Proofs
