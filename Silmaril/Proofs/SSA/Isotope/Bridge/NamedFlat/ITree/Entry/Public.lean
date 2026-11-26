module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Conservativity.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public (Readback)
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA.Semantics (Env)
open Silmaril.Elgot.ITree (HandledTrace HasTrace)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {a b : Nat} {inputs : Fin a → PacketType}
  {outputs : Fin b → PacketType} {left right : Program signature inputs outputs} {input : Fin a}
  {source target : CFG V K F} {exits : List K} {fields : K → List V}

private theorem run_tree_at (entry : Program.PackedEntry left input) (r : Readback entry source exits fields)
    (initial : V → Value Atom) (record : Env Atom)
    (captures : ∀ i, record i.val = initial (r.captures i)) :
    (runSSA (treeModel signature.primitive) (LiveOut.attach fields source) initial >>=
      fun out => pure (treeExitNumber exits out)) =
        LambdaSSA.Semantics.Interaction.region signature.primitive record r.flat.erase := by
  obtain ⟨captureCount, names, _, _, blocks, count, flat, accepted, _⟩ := r
  subst blocks
  exact Silmaril.Isotope.Bridge.NamedFlat.run_tree signature.primitive _ exits names
    ((Silmaril.Isotope.Bridge.NamedFlat.elaborateAt_eq _ exits names).symm.trans accepted) initial record captures

theorem observe_eq (entry : Program.PackedEntry left input) (readback : Readback entry source exits fields)
    (initial : V → Value Atom) (ambient record : Env Atom)
    (captures : ∀ i, record i.val = initial (readback.captures i)) :
    entry.observe ambient record = Entry.LiveOut.observeRaw signature.primitive exits fields source initial := by
  let _ := signature.typing
  unfold Program.PackedEntry.observe
  rw [Capture.packed_context_tree signature.primitive entry.typed ambient record, ← readback.agrees,
    ← run_tree_at entry readback initial record captures, bind_assoc]
  unfold Entry.LiveOut.observeRaw
  rw [← RoundTrip.run_packetClosed_obs (treeModel signature.primitive) _ readback.closed initial,
    Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.run_project]
  simp only [pure_bind, bind_map_left]

theorem refinementAt_namedHandledTrace [DecidableEq F] (packet : Denote (inputs input))
    (leftEntry : Program.PackedEntry left input) (rightEntry : Program.PackedEntry right input)
    (l : Readback leftEntry source exits fields) (r : Readback rightEntry target exits fields)
    (initial : V → Value Atom) (leftAmbient rightAmbient leftRecord rightRecord : Env Atom)
    (leftCaptures : ∀ i, leftRecord i.val = initial (l.captures i))
    (rightCaptures : ∀ i, rightRecord i.val = initial (r.captures i))
    (leftAgrees : leftEntry.recordAgrees packet leftRecord)
    (rightAgrees : rightEntry.recordAgrees packet rightRecord) :
    left.refinementAt? right input packet = true ↔
      ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
        ∀ x, policy.initial x → ∀ p,
          HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields source initial) p →
          HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields target initial) p := by
  refine (Program.refinementAt?_iff_valid_traceSat packet leftEntry rightEntry leftAmbient rightAmbient
    leftRecord rightRecord leftAgrees rightAgrees).trans ?_
  change (∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
    ∀ x, policy.initial x → ∀ p, HandledTrace policy.step x (leftEntry.observe leftAmbient leftRecord) p →
      HasTrace (rightEntry.observe rightAmbient rightRecord) p) ↔ _
  rw [observe_eq leftEntry l initial leftAmbient leftRecord leftCaptures,
    observe_eq rightEntry r initial rightAmbient rightRecord rightCaptures]
  exact ⟨fun h policy x initial p seen => ⟨h policy x initial p seen, seen.2⟩,
    fun h policy x initial p seen => (h policy x initial p seen).1⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public
