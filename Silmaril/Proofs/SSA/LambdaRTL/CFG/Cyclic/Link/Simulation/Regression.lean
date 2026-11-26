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

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
