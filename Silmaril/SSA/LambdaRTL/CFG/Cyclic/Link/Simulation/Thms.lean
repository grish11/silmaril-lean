module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.PacketCopy
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Soundness
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Composition

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

open Comparison

variable {V F α : Type} [DecidableEq V] {a b c : Nat}

theorem PacketCopy.target?_eq_some_iff {K : Type} {available : Finset V}
    {body : Body V K F} {target : K} :
    PacketCopy.target? available body = some target ↔ PacketCopy.Forwards available body target :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.target_iff

/-- A typed read gets the packet at every step. The returned label is the
checked jump target and the returned value is the original packet. -/
theorem PacketCopy.Forwards.evalJump {K : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    {available : Finset V} {body : Body V K F} {target : K}
    (typed : PacketCopy.Forwards available body target)
    (model : Model F M α) (store : V → α) (packet : α)
    (agrees : ∀ reg ∈ available, store reg = packet) :
    body.evalJump model store = pure (target, packet) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.evalJump model typed store packet agrees

/-- On entry, the block parameter alone is typed as holding the packet.
Other incoming register values may be arbitrary. -/
theorem PacketCopy.Forwards.evalJump_packet {K : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
    {source : Block V K F} {target : K} (typed : PacketCopy.Forwards {source.param} source.body target)
    (model : Model F M α) (store : V → α) (packet : α) :
    source.body.evalJump model (upd store source.param packet) = pure (target, packet) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.evalJump_packet model source typed store packet

theorem Simulation.check_iff [DecidableEq F] (left right : Graph V F a b)
    (address : Fin left.locals → Label right.locals b) :
    Simulation.check left right address = true ↔
      (∀ port, Sum.elim address Sum.inr (left.entry port) = right.entry port) ∧
      (∀ i, BlockMatch right (Sum.elim address Sum.inr) (left.block i) (address i)) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.check_iff left right address

/-- Turn a successful finite check into the corresponding syntactic simulation. -/
def Simulation.ofCheck [DecidableEq F] (left right : Graph V F a b)
    (address : Fin left.locals → Label right.locals b) (passed : Simulation.check left right address = true) :
    Simulation left right :=
  ⟨address, ((Simulation.check_iff left right address).mp passed).1,
    ((Simulation.check_iff left right address).mp passed).2⟩

/-- A syntactic certificate transports every finite successful result. -/
theorem Simulation.denote_le {left right : Graph V F a b} (sim : Simulation left right)
    (model : Model F Part α) (input : Fin a × α) : left.denote model input ≤ right.denote model input :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.denote_le sim model input

theorem Simulation.refines {left right : Graph V F a b} (sim : Simulation left right) :
    Refines (Quotient.mk _ left : Arrow V F α a b) (Quotient.mk _ right) :=
  fun model input => sim.denote_le model.val input

/-- Linking certificates is a syntactic operation, with a local rule for each
of the two private ranges and for each handoff. -/
def Simulation.link [Inhabited V] {left left' : Graph V F a b} {right right' : Graph V F b c}
    (first : Simulation left left') (second : Simulation right right') :
    Simulation (left.link right) (left'.link right') where
  address := first.linkedAddress second
  entry := by exact Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.link_entry first second
  block := by exact Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.link_block first second

/-- Soundness in the named refinement interface at each input port. -/
theorem Simulation.namedSSA_sat [Inhabited V] {left right : Graph V F a b} (sim : Simulation left right)
    (model : PairModel F Part α) (port : Fin a) :
    Cyclic.Institution.Refinement.ssaSat model
      (namedSSAClass port (Quotient.mk _ left)) (namedSSAClass port (Quotient.mk _ right)) :=
  (namedSSA_sat_iff model _ _).mpr (sim.refines model) port

theorem Graph.denote_wiring (model : Model F Part α) (wire : Fin a → Fin b) (input : Fin a × α) :
    (Graph.wiring (V := V) (F := F) wire).denote model input = pure (wire input.1, input.2) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.denote_wiring model wire input

/-- For graphs with only direct wires, a single model detects any mismatch.
Uniform refinement therefore gives a syntactic certificate in this fragment. -/
def wiring_complete (model : PairModel F Part α) (left right : Fin a → Fin b)
    (included : Refines (Quotient.mk _ (Graph.wiring left) : Arrow V F α a b)
      (Quotient.mk _ (Graph.wiring right))) :
    Simulation (Graph.wiring (V := V) (F := F) left) (Graph.wiring right) where
  address := Fin.elim0
  block i := Fin.elim0 i
  entry port := by
    have atPort : (Graph.wiring (V := V) (F := F) left).denote model.val (port, model.val.unit) ≤
        (Graph.wiring (V := V) (F := F) right).denote model.val (port, model.val.unit) :=
      included model (port, model.val.unit)
    rw [Graph.denote_wiring, Graph.denote_wiring] at atPort
    have equal : (left port, model.val.unit) = (right port, model.val.unit) :=
      Part.mem_some_iff.mp (atPort _ (Part.mem_some _))
    exact congrArg (fun output : Fin b × α => Sum.inr output.1) equal

/-- Completeness against a direct wire when every source private block
has a typed copy sequence that jumps directly to a public port. -/
def directCopies_complete (model : PairModel F Part α) (source : Graph V F a b)
    (exit : Fin source.locals → Fin b)
    (typed : ∀ i, PacketCopy.Forwards {(source.block i).param} (source.block i).body (.inr (exit i)))
    (wire : Fin a → Fin b)
    (included : Refines (Quotient.mk _ source : Arrow V F α a b) (Quotient.mk _ (Graph.wiring wire))) :
    Simulation source (Graph.wiring wire) where
  address i := .inr (exit i)
  block i := .forwardCopies (.inr (exit i)) (typed i) rfl
  entry := by
    exact Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.directCopies_entry
      model source exit typed wire included

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
