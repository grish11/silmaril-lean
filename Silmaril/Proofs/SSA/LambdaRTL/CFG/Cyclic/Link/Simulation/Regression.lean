module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Thms
import Mathlib.Data.Nat.Pairing

/-! A forwarding loop strictly refines the wire. An ordered register copy
certifies against the wire, including after linking. These examples use an
empty alphabet. -/

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

open Silmaril.Elgot
open Comparison

private def wire : Graph Bool Empty 1 1 := Graph.wiring id

private def spin : Graph Bool Empty 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨false, .term (.br (.inl 0) (.var false))⟩
  closed _ := by simp [Body.toRegion, Term.toRegion, Region.fv, Val.fv]

private def move : Graph Bool Empty 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨false, .let1 true (.val (.var false)) (.term (.br (.inr 0) (.var true)))⟩
  closed _ := by simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

private def altered : Graph Bool Empty 1 1 where
  locals := 1
  entry _ := .inl 0
  block _ := ⟨false, .let1 true (.val (.var false))
    (.term (.br (.inr 0) (.pair (.var true) .unit)))⟩
  closed _ := by simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

private def model : PairModel Empty Part Nat :=
  ⟨{ unit := 0
     pair := Nat.pair
     inl := id
     inr := Nat.succ
     unpair n := pure (Nat.unpair n)
     split n := pure (.inl n)
     app symbol := symbol.elim
     abort _ := Part.none },
   ⟨fun left right => congrArg Part.some (Nat.unpair_pair left right)⟩⟩

private def spinToWire : Simulation spin wire :=
  Simulation.ofCheck spin wire (fun _ => .inr 0) (by decide)

private def wireToWire : Simulation wire wire :=
  Simulation.ofCheck wire wire Fin.elim0 (by decide)

private def moveToWire : Simulation move wire :=
  Simulation.ofCheck move wire (fun _ => .inr 0) (by decide)

example : Simulation.check (spin.link wire) (wire.link wire)
    (spinToWire.link wireToWire).address = true := by decide

example : Simulation.check (move.link wire) (wire.link wire)
    (moveToWire.link wireToWire).address = true := by decide

example : Simulation.check altered wire (fun _ => .inr 0) = false := by decide

example : (altered.block (0 : Fin 1)).body.evalJump model.val (upd (fun _ => 0) false 2) =
    Part.some (.inr 0, 6) := by
  simp [altered, model, Body.evalJump, Body.exec, Term.exec, Op.eval, Val.eval, upd,
    Nat.pair, Part.pure_eq_some]

private def ordered : Body Nat Unit Empty :=
  .let1 1 (.val (.var 0)) (.let1 2 (.val (.var 1)) (.term (.br () (.var 2))))

private def reordered : Body Nat Unit Empty :=
  .let1 2 (.val (.var 1)) (.let1 1 (.val (.var 0)) (.term (.br () (.var 2))))

example : PacketCopy.target? {0} ordered = some () := by decide
example : PacketCopy.target? {0} reordered = none := by decide

private theorem spin_none (m : Model Empty Part Nat) (packet : Nat) :
    spin.denote m (0, packet) = Part.none := by
  let stay (n : Nat) : Part ((Fin 1 × Nat) ⊕ Nat) := pure (.inr n)
  let state (n : Nat) : Label spin.locals 1 × Nat := (.inl (0 : Fin 1), n)
  have commute : (stay >=> liftPure (Sum.map id state)) =
      (liftPure state >=> spin.step m) := by
    funext n
    simp [stay, state, liftPure, Bind.kleisliRight, spin, Graph.step,
      Body.evalJump, Body.exec, Term.exec, Val.eval, upd]
  have run := congrFun (LawfulElgotMonad.uniformity stay (spin.step m) state commute) packet
  change iter stay packet = (pure (state packet) >>= iter (spin.step m)) at run
  rw [pure_bind] at run
  exact run.symm.trans (Silmaril.Elgot.Part.iter_forever packet)

private noncomputable def spinClass : Arrow Bool Empty Nat 1 1 := Quotient.mk _ spin
private noncomputable def wireClass : Arrow Bool Empty Nat 1 1 := Quotient.mk _ wire
private noncomputable def moveClass : Arrow Bool Empty Nat 1 1 := Quotient.mk _ move

theorem cyclic_strict : Refines spinClass wireClass ∧ ¬ Refines wireClass spinClass := by
  refine ⟨spinToWire.refines, ?_⟩
  intro reversed
  have included : wire.denote model.val (0, 0) ≤ spin.denote model.val (0, 0) :=
    reversed model (0, 0)
  rw [spin_none, wire, Graph.denote_wiring] at included
  exact Part.notMem_none _ (included _ (Part.mem_some _))

private theorem move_denote (m : Model Empty Part Nat) (input : Fin 1 × Nat) :
    move.denote m input = pure input := by
  have entry : move.step m (.inl (0 : Fin 1), input.2) = pure (.inr (.inr 0, input.2)) := by
    simp [move, Graph.step, Body.evalJump, Body.exec, Term.exec, Op.eval, Val.eval, upd]
  change iter (move.step m) (.inl (0 : Fin 1), input.2) = pure input
  rw [congrFun (LawfulElgotMonad.fixpoint _) _, entry, pure_bind]
  change iter (move.step m) (.inr 0, input.2) = pure input
  rw [congrFun (LawfulElgotMonad.fixpoint _) _]
  simp [Graph.step, Subsingleton.elim (0 : Fin 1) input.1]

theorem one_copy_refines : Refines moveClass wireClass := moveToWire.refines

example : Simulation move wire :=
  directCopies_complete model move (fun _ => 0)
    (fun _ => PacketCopy.target?_eq_some_iff.mp (by simp [move, PacketCopy.target?])) id (by
      intro m input
      have same : move.denote m.val input = wire.denote m.val input := by
        rw [move_denote, wire, Graph.denote_wiring]
        rfl
      exact same.le)

private def copyTable {n b : Nat} (entry : Label n b) (edges : Fin n → Label n b) :
    Graph Bool Empty 1 b where
  locals := n
  entry _ := entry
  block i := ⟨false, .let1 true (.val (.var false)) (.term (.br (edges i) (.var true)))⟩
  closed _ := by simp [Body.toRegion, Term.toRegion, Region.fv, Op.fv, Val.fv]

-- Two private blocks forward to exit 0. The unused block forwards to exit 1.
private def chain : Graph Bool Empty 1 2 :=
  copyTable (n := 3) (.inl 0) fun i =>
    if i = 0 then .inl 1 else if i = 1 then .inr 0 else .inr 1

private def chainWire : Graph Bool Empty 1 2 := Graph.wiring (fun _ => 0)

private def chainCertificate : Simulation chain chainWire :=
  CopyChain.certificate chain (fun _ => 0) (by decide)

example : CopyChain.terminalWithin? chain 1 (.inl (0 : Fin 3)) = none := by decide
example : chainCertificate.address (2 : Fin 3) = .inr 1 := by decide
example : CopyChain.check chain (fun _ => 1) = false := by decide

example (m : Model Empty Part Nat) (packet : Nat) :
    chain.denote m (0, packet) = pure (0, packet) :=
  CopyChain.denote_of_terminal m (0, packet) 0 (by
    change CopyChain.terminal? chain (chain.entry 0) = some 0
    decide)

private def swapPorts (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0
private def swapWire : Graph Bool Empty 2 2 := Graph.wiring swapPorts

private def swapCertificate : Simulation swapWire swapWire :=
  CopyChain.certificate swapWire swapPorts (by decide)

example : Simulation.check (chain.link swapWire) (chainWire.link swapWire)
    (chainCertificate.link swapCertificate).address = true := by decide

example : CopyChain.check (chain.link swapWire) (fun _ => 1) = true := by decide

private def ring (entry : Label 2 1) : Graph Bool Empty 1 1 :=
  copyTable entry fun i => .inl (if i = 0 then 1 else 0)

example : CopyChain.check (ring (.inl 0)) id = false := by decide

-- The old forward simulation can stutter forever. It still proves inclusion.
example : Simulation.check (ring (.inl 0)) wire (fun _ => .inr 0) = true := by decide

theorem reachable_cycle_diverges (m : Model Empty Part Nat) (packet : Nat) :
    (ring (.inl 0)).denote m (0, packet) = Part.none :=
  CopyChain.denote_none m (0, packet)
    (by intro i; simp [ring, copyTable, CopyChain.next?, PacketCopy.target?]) (by
      change CopyChain.terminal? (ring (.inl 0)) ((ring (.inl 0)).entry 0) = none
      decide)

example : CopyChain.check (ring (.inr 0)) id = false := by decide

-- A cycle in the unused table is invisible to the observations at inputs.
example (m : Model Empty Part Nat) (input : Fin 1 × Nat) :
    (ring (.inr 0)).denote m input = wire.denote m input := by
  rw [wire, Graph.denote_wiring,
    CopyChain.denote_of_terminal m input input.1 (by
      have port : input.1 = 0 := Subsingleton.elim _ _
      rw [port]
      rfl)]
  rfl

private theorem reachable_ring_outcome :
    CopyChain.entryOutcome (ring (.inl 0)) 0 = .cycle (0 : Fin 2) := by cbv

private theorem reachable_ring_verdict : CopyChain.refinement? (ring (.inl 0)) id = some true := by cbv

example : CopyChain.refinement? (ring (.inr 0)) id = some true := by cbv

example : CopyChain.LoopsAt (ring (.inl 0)) (0 : Fin 2) :=
  (CopyChain.entryOutcome_cycle (graph := ring (.inl 0)) model.val (0, 0) (0 : Fin 2)
    reachable_ring_outcome).1.2

example : Refines (Quotient.mk _ (ring (.inl 0)) : Arrow Bool Empty Nat 1 1) (Quotient.mk _ wire) :=
  ((CopyChain.refinement?_eq_some_iff model (ring (.inl 0)) id true).mp reachable_ring_verdict).2.mp rfl

example : CopyChain.entryOutcome chain 0 = .returns 0 := by cbv

private theorem wrong_wire_verdict : CopyChain.refinement? chain (fun _ => 1) = some false := by cbv

example : ¬ Refines (Quotient.mk _ chain : Arrow Bool Empty Nat 1 2)
    (Quotient.mk _ (Graph.wiring (fun _ => 1))) := by
  have mismatch := ((CopyChain.refinement?_eq_some_iff model chain (fun _ => 1) false).mp wrong_wire_verdict).2
  exact fun included => Bool.noConfusion (mismatch.mpr included)

-- The altered block remains unsupported after two checked jumps.
example : CopyChain.entryOutcome (move.link altered) 0 = .unsupported (2 : Fin 3) := by cbv
example : CopyChain.refinement? (move.link altered) id = none := by cbv

private def unusedAltered : Graph Bool Empty 1 1 := { altered with entry := fun _ => .inr 0 }

example : CopyChain.refinement? unusedAltered id = some true := by cbv

-- The cycle labels are local to their graphs, which have different sizes.
example : CopyChain.refinementBetween? spin (ring (.inl 0)) = some true := by cbv
example : CopyChain.refinementBetween? (ring (.inl 0)) spin = some true := by cbv

private def shortChain (port : Fin 2) : Graph Bool Empty 1 2 :=
  copyTable (n := 1) (.inl 0) fun _ => .inr port

example : CopyChain.refinementBetween? (shortChain 0) chain = some true := by cbv
example : CopyChain.refinementBetween? chain (shortChain 0) = some true := by cbv
example : CopyChain.refinementBetween? chain (shortChain 1) = some false := by cbv

example : CopyChain.refinementBetween? (ring (.inl 0)) move = some true := by cbv

private theorem return_to_cycle_verdict :
    CopyChain.refinementBetween? move (ring (.inl 0)) = some false := by cbv

example : ¬ Refines moveClass (Quotient.mk _ (ring (.inl 0))) := by
  have failed := ((CopyChain.refinementBetween?_eq_some_iff model move (ring (.inl 0)) false).mp
    return_to_cycle_verdict).2
  exact fun included => Bool.noConfusion (failed.mpr included)

example : CopyChain.refinementBetween? (ring (.inl 0)) altered = none := by cbv
example : CopyChain.refinementBetween? altered (ring (.inl 0)) = none := by cbv
example : CopyChain.refinementBetween? move unusedAltered = some true := by cbv

-- A left cycle never enters the right table, even when that input is unsupported.
example : CopyChain.entryOutcome ((ring (.inl 0)).link altered) 0 = .cycle (0 : Fin 4) := by
  rw [CopyChain.entryOutcome_link, reachable_ring_outcome]
  rfl

example : CopyChain.entryOutcome (move.link (ring (.inl 0))) 0 = .cycle (2 : Fin 4) := by
  rw [CopyChain.entryOutcome_link]
  cbv

private def selectiveRight : Graph Bool Empty 2 1 where
  locals := altered.locals
  entry mid := if mid = 0 then .inr 0 else altered.entry 0
  block := altered.block
  closed := altered.closed

example : CopyChain.entryOutcome ((shortChain 0).link selectiveRight) 0 = .returns 0 := by
  rw [CopyChain.entryOutcome_link]
  cbv

example : CopyChain.entryOutcome ((shortChain 1).link selectiveRight) 0 = .unsupported (3 : Fin 4) := by
  rw [CopyChain.entryOutcome_link]
  cbv

private def linkedChain : Graph Bool Empty 1 2 := chain.link swapWire
private def linkedShort (port : Fin 2) : Graph Bool Empty 1 2 := (shortChain port).link swapWire

private def renamedModel : PairModel Bool Part Nat :=
  ⟨{ model.val with app := fun op packet => pure (if op then packet + 1 else packet) },
    ⟨fun left right => congrArg Part.some (Nat.unpair_pair left right)⟩⟩

example : ∀ input, Cyclic.Institution.Refinement.ssaSat renamedModel
    (namedSSAClass input (Quotient.mk _ (linkedChain.mapOp Empty.elim)))
    (namedSSAClass input (Quotient.mk _ ((linkedShort 0).mapOp Empty.elim))) := by
  have passed : CopyChain.refinementBetween? linkedChain (linkedShort 0) = some true := by cbv
  exact ((CopyChain.refinementBetween?_eq_some_namedSSA_map_iff Empty.elim renamedModel
    linkedChain (linkedShort 0) true).mp passed).2.mp rfl

example : ¬ (∀ input, Cyclic.Institution.Refinement.ssaSat model
    (namedSSAClass input (Quotient.mk _ linkedChain))
    (namedSSAClass input (Quotient.mk _ (linkedShort 1)))) := by
  have failed : CopyChain.refinementBetween? linkedChain (linkedShort 1) = some false := by cbv
  have verdictSound := ((CopyChain.refinementBetween?_eq_some_namedSSA_iff model
    linkedChain (linkedShort 1) false).mp failed).2
  exact fun satisfied => Bool.noConfusion (verdictSound.mpr satisfied)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
