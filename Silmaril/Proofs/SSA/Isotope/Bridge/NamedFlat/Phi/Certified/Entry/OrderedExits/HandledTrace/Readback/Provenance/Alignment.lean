module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Provenance.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Provenance.Codec
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Scoped.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.Provenance

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
open Silmaril.SSA.LambdaRTL (Val)
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive Transfer region splitTransfer term flat_tree_of_agree)

universe u v
variable {Events : Type u → Type u} {F : Type v} {α β : Type (u + 1)}
  {blocks publicBlocks exits publicExits captures publicCaptures : Nat}
  {source : FiniteCFG F blocks exits captures} {target : FiniteCFG F publicBlocks publicExits publicCaptures}
  {left : Primitive Events F α} {right : Primitive Events F β}
  {leftEnv : Env α} {rightEnv : Env β} {atom : α → β}

theorem packet_tree (instr : Primitive Events F α) (env : Env α) (packet : Val (Fin captures)) :
    term instr env (packetTerm packet) = pure (packetValue env packet) := by
  induction packet <;> simp [packetTerm, packetValue, term, *]

private theorem split_codec (count : blocks = publicBlocks) (atom : α → β) (out : Transfer α) :
    Sum.map (resultCodec atom) (stateCodec count atom) (splitTransfer blocks out) =
      splitTransfer publicBlocks (resultCodec atom out) := by
  subst publicBlocks
  rcases out with ⟨i, value⟩
  by_cases localLabel : i < blocks <;> simp [splitTransfer, stateCodec, resultCodec, localLabel]

def sameGraph (prim : PrimitivesAgree left right atom) (graph : FiniteCFG F blocks exits captures)
    (env : Env α) : Alignment graph graph left right env (valueCodec atom ∘ env) atom := by
  have localTransfer {labels n : Nat} (body : LambdaSSA.Flat F labels n) (localEnv : Env α) :
      Sum.map (resultCodec atom) (stateCodec (rfl : blocks = blocks) atom) <$>
        transfer left localEnv blocks body =
        transfer right (valueCodec atom ∘ localEnv) blocks body := by
    unfold transfer
    rw [← flat_codec prim]
    simp only [← bind_pure_comp, bind_assoc, pure_bind, split_codec]
  refine ⟨stateCodec rfl atom, localTransfer graph.entry env, fun pending => ?_⟩
  change _ = transfer right (extend (valueCodec atom ∘ env) (valueCodec atom pending.2))
    blocks (graph.block pending.1)
  have mapped : valueCodec atom ∘ extend env pending.2 =
      extend (valueCodec atom ∘ env) (valueCodec atom pending.2) := by
    funext i
    cases i <;> rfl
  exact (localTransfer (graph.block pending.1) (extend env pending.2)).trans
    (congrArg (fun localEnv => transfer right localEnv blocks (graph.block pending.1)) mapped)

theorem entry (p : Provenance source target)
    (packet : rightEnv p.slot.val =
      valueCodec atom (packetValue leftEnv p.seed)) :
    Sum.map (resultCodec atom) (stateCodec p.count atom) <$> transfer left leftEnv blocks source.entry =
      transfer right rightEnv publicBlocks target.entry := by
  unfold transfer
  rw [p.sourceEntry, p.publicEntry]
  simp only [region, packet_tree, term, pure_bind, map_pure, packet]
  exact congrArg pure (split_codec p.count atom _)

theorem block (p : Provenance source target) (prim : PrimitivesAgree left right atom)
    (state : BlockInput α blocks) :
    Sum.map (resultCodec atom) (stateCodec p.count atom) <$> blockStep left source leftEnv state =
      blockStep right target rightEnv (stateCodec p.count atom state) := by
  have same :
      resultCodec atom <$> region left (extend leftEnv state.2) (source.block state.1).erase =
        region right (extend rightEnv (valueCodec atom state.2)) (target.block (state.1.cast p.count)).erase := by
    rw [p.sourceRow, p.publicRow]
    apply (flat_codec prim _ _).trans
    apply flat_tree_of_agree
    intro i
    have zero : i.val = 0 := Nat.le_zero.mp (Nat.lt_succ_iff.mp i.isLt)
    rw [zero]
    rfl
  change _ <$> (splitTransfer blocks <$> _) = splitTransfer publicBlocks <$>
    region right (extend rightEnv (valueCodec atom state.2)) (target.block (state.1.cast p.count)).erase
  rw [← same]
  simp only [← bind_pure_comp, bind_assoc, pure_bind, split_codec]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.Provenance

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

theorem public_entry {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
    {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
    {program : Program signature inputs outputs} {input : Fin a}
    (entry : Program.PackedEntry program input) (slot : Fin entry.count)
    (idx : Fin ((program.compile input).blocks.length + program.exits.length))
    (found : first entry.captures ⟨0⟩ = some slot)
    (label : labelIndex (program.compile input).blocks program.exits ⟨program.entry input⟩ = some idx) :
    entry.target.entry.erase = .br idx.val (.var slot.val) := by
  let number := labelIndex (program.compile input).blocks program.exits
  have written : (program.compile input).entry =
      .term (.br ⟨program.entry input⟩ (.var ⟨0⟩)) := rfl
  have compiled : body number (first entry.captures) (program.compile input).entry =
      some (LambdaSSA.Flat.br idx (.bv slot)) := by
    rw [written]
    simp [body, term, value, found, number, label]
  have accepted := entry.accepted
  change ((body number (first entry.captures) (program.compile input).entry).bind fun code =>
    (tabulate _ fun i =>
      body number (blockNames (program.compile input).blocks[i].2.param)
        (program.compile input).blocks[i].2.body).map fun table => ⟨code, table⟩) = some entry.target at accepted
  simp only [compiled, Option.bind_some, Option.map_eq_some_iff] at accepted
  obtain ⟨rows, _, equal⟩ := accepted
  exact congrArg (fun graph => graph.entry.erase) equal.symm

theorem capture_packet {F : Type} {signature : PrimitiveSignature F} {a b : Nat}
    {inputs : Fin a → PacketType} {outputs : Fin b → PacketType}
    {program : Program signature inputs outputs} {input : Fin a}
    (entry : Program.PackedEntry program input) (slot : Fin entry.count)
    (found : first entry.captures ⟨0⟩ = some slot)
    (packet : Denote (inputs input)) (env : LambdaSSA.Semantics.Env Atom)
    (agrees : entry.recordAgrees packet env) :
    env slot.val = PacketType.encode (inputs input) packet := by
  unfold first at found
  have slotName : entry.captures slot = ⟨0⟩ :=
    of_decide_eq_true (List.find?_some (p := fun i : Fin entry.count => decide (entry.captures i = ⟨0⟩)) found)
  rw [agrees slot, slotName]
  simp [Program.store, Silmaril.SSA.LambdaRTL.upd]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
