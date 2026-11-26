module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Institution.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.RegisterRename.Thms

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open Phi.Certified.Entry.OrderedExits.Readback (Provenance)

variable {V W K : Type 1} [DecidableEq V] [DecidableEq W] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType : PacketType} {outputs : Fin exits.length → PacketType}

namespace StructuralEntry

/-- Transport exact readback across equal counts, keeping its positional seed
and row proofs together with the flat table they describe. -/
def castReadback {m n m' n' p q r exitCount : Nat} {target : FiniteCFG F p q r}
    (blocks : m = m') (captures : n = n')
    (data : Σ flat : FiniteCFG F m exitCount n, Σ proof : Provenance flat target,
      StructuralSeed proof.seed inputType) :
    Σ flat : FiniteCFG F m' exitCount n', Σ proof : Provenance flat target,
      StructuralSeed proof.seed inputType :=
  blocks ▸ captures ▸ data

private theorem accepted_castReadback {m n p q r : Nat} {target : FiniteCFG F p q r}
    (g : CFG W K F) (names : List W) (blocks : m = g.blocks.length) (captures : n = names.length)
    (data : Σ flat : FiniteCFG F m exits.length n, Σ proof : Provenance flat target,
      StructuralSeed proof.seed inputType)
    (accepted : elaborateAt g exits (fun i => names[(i.cast captures).val]) m blocks.symm = some data.1) :
    elaborate g exits (fun i => names[i.val]) = some (castReadback blocks captures data).1 := by
  subst m
  subst n
  exact (elaborateAt_eq g exits _).symm.trans accepted

private theorem accepted_renamed {m n : Nat} (rename : V ↪ W) (g : CFG V K F)
    (g' : CFG W K F) (mapped : g' = RoundTrip.renameGraph rename g)
    (names : Fin n → V) (len : g.blocks.length = m) (len' : g'.blocks.length = m) :
    elaborateAt g' exits (rename ∘ names) m len' = elaborateAt g exits names m len := by
  subst g'
  exact elaborateAt_rename rename g exits names m len len'

/-- Rename the actual named syntax and selected live-outs, reusing the very
same checked packed dispatcher and the exact positional readback. -/
def rename (entry : StructuralEntry signature source exits fields inputType outputs) (names : V ↪ W) :
    StructuralEntry signature (RoundTrip.renameGraph names source) exits
      (fun k => (fields k).map names) inputType outputs :=
  let renamed := LiveOut.attach (fun k => (fields k).map names) (RoundTrip.renameGraph names source)
  let captures := entry.names.map names
  have attach := RegisterRename.attach_rename names fields source
  have sameBlocks : (LiveOut.attach fields source).blocks.length = renamed.blocks.length :=
    (List.length_map ..).symm.trans (congrArg (fun g => g.blocks.length) attach).symm
  have sameCaptures : entry.names.length = captures.length := (List.length_map ..).symm
  let readback := castReadback sameBlocks sameCaptures
    ⟨entry.flat, entry.provenance, entry.typedSeed⟩
  have sameNames : (fun i : Fin entry.names.length => captures[(i.cast sameCaptures).val]) =
      names ∘ fun i => entry.names[i.val] := by
    funext i
    exact List.getElem_map ..
  have accepted : elaborate renamed exits (fun i => captures[i.val]) = some readback.1 := by
    apply accepted_castReadback
    rw [sameNames, accepted_renamed names (LiveOut.attach fields source) renamed attach
      (fun i => entry.names[i.val]) rfl sameBlocks.symm, elaborateAt_eq]
    exact entry.accepted
  ⟨captures, entry.program, entry.entry, attach ▸ RegisterRename.closed_rename names _ entry.closed,
    readback.1, accepted, readback.2.1, readback.2.2, entry.publicCaptures⟩

end StructuralEntry

/-- Pull a named store along the inverse register equivalence. -/
def renameStore (names : V ≃ W) (initial : V → Value Atom) : W → Value Atom :=
  initial ∘ names.symm

/-- Transport the concrete named store in a directed witness. Its typed
exchanges and terminal exit/live-out observation keep their exact values. -/
def CaptureTraceWitness.rename (witness : CaptureTraceWitness V signature)
    (names : V ≃ W) : CaptureTraceWitness W signature :=
  ⟨renameStore names witness.initial, witness.trace⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
