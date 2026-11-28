module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.InstructionMap.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.InstructionMap.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.InstructionMap.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Compilation

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)

variable {F G : Type} {s : PrimitiveSignature F} {t : PrimitiveSignature G}

private theorem accepted_at {V K : Type 1} [DecidableEq V] [DecidableEq K] {n b : Nat}
    (graph : CFG V K G) (exits : List K) (names : Fin n → V) (length : graph.blocks.length = b)
    {code : FiniteCFG G b exits.length n}
    (accepted : elaborateAt graph exits names b length = some code) :
    elaborate graph exits names = some (length.symm ▸ code) := by
  subst b
  exact (elaborateAt_eq graph exits names).symm.trans accepted

theorem accepted_map {V K : Type 1} [DecidableEq V] [DecidableEq K]
    (opcode : F → G) (graph : CFG V K F) (mapped : CFG V K G)
    (written : (graph.mapOp opcode) = mapped) (exits : List K) {n : Nat} (names : Fin n → V)
    (length : graph.blocks.length = mapped.blocks.length)
    {code : FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits names = some code) :
    elaborate mapped exits names = some (length ▸ code.mapInstr opcode) := by
  subst mapped
  apply accepted_at (graph.mapOp opcode) exits names length.symm
  rw [elaborateAt_mapOp opcode graph exits names _ rfl length.symm, elaborateAt_eq, accepted]
  rfl

theorem typed_map {b b' e n : Nat} (rename : s.Renaming t)
    (length : b = b') {context : BoundCtx PacketType n} {blocks : Fin b → PacketType}
    {exits : Fin e → PacketType} {code : FiniteCFG F b e n}
    (typed : letI := s.typing; code.HasType context blocks exits) :
    letI := t.typing
    (show FiniteCFG G b' e n from length ▸ code.mapInstr rename.opcode).HasType context (fun i => blocks (i.cast length.symm)) exits := by
  subst b'
  let _ := s.typing
  let _ := t.typing
  exact typed.mapInstr ⟨rename.argument, rename.reply⟩

theorem packet_closed_map {V K : Type 1} [DecidableEq V] (opcode : F → G) {graph : CFG V K F}
    (closed : RoundTrip.PacketClosed graph) : RoundTrip.PacketClosed (graph.mapOp opcode) := by
  intro item hin
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hin
  simpa only [CFG.Block.mapOp, CFG.Body.toRegion_mapOp, Silmaril.SSA.LambdaRTL.Region.fv_mapOp] using closed old hold

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Occurrences.Compilation
