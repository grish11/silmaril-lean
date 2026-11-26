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
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (region)
open Silmaril.Elgot.ITree (HandledTrace HasTrace)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {a b : Nat} {inputs : Fin a → PacketType}
  {outputs : Fin b → PacketType} {left right : Program signature inputs outputs} {input : Fin a}
  {source target : CFG V K F} {exits : List K} {fields : K → List V}

theorem observeRaw_eq_flat {n : Nat}
    (signature : PrimitiveSignature F) (source : CFG V K F) (exits : List K) (fields : K → List V)
    (names : Fin n → V) {flat : FiniteCFG F (LiveOut.attach fields source).blocks.length exits.length n}
    (closed : RoundTrip.PacketClosed (LiveOut.attach fields source))
    (accepted : elaborate (LiveOut.attach fields source) exits names = some flat)
    (initial : V → Value Atom) (record : Env Atom)
    (captures : ∀ i, record i.val = initial (names i)) :
    Entry.LiveOut.observeRaw signature.primitive exits fields source initial =
      (region signature.primitive record flat.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) := by
  rw [← run_tree signature.primitive _ exits names accepted initial record captures, bind_assoc]
  unfold Entry.LiveOut.observeRaw
  rw [← RoundTrip.run_packetClosed_obs (treeModel signature.primitive) _ closed initial,
    Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.run_project]
  simp only [pure_bind, bind_map_left]

theorem observe_eq (entry : Program.PackedEntry left input) (readback : Readback entry source exits fields)
    (initial : V → Value Atom) (ambient record : Env Atom)
    (captures : ∀ i, record i.val = initial (readback.captures i)) :
    entry.observe ambient record = Entry.LiveOut.observeRaw signature.primitive exits fields source initial := by
  obtain ⟨_, names, _, closed, blocks, count, flat, accepted, agrees⟩ := readback
  subst blocks
  let _ := signature.typing
  unfold Program.PackedEntry.observe
  rw [Capture.packed_context_tree signature.primitive entry.typed ambient record, ← agrees,
    observeRaw_eq_flat signature source exits fields names closed
      ((elaborateAt_eq _ exits names).symm.trans accepted) initial record captures]

theorem refinementAt_namedHandledTrace_of_observe_eq [DecidableEq F] (packet : Denote (inputs input))
    (leftEntry : Program.PackedEntry left input) (rightEntry : Program.PackedEntry right input)
    (initial : V → Value Atom) (leftAmbient rightAmbient leftRecord rightRecord : Env Atom)
    (leftObs : leftEntry.observe leftAmbient leftRecord =
      Entry.LiveOut.observeRaw signature.primitive exits fields source initial)
    (rightObs : rightEntry.observe rightAmbient rightRecord =
      Entry.LiveOut.observeRaw signature.primitive exits fields target initial)
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
  rw [leftObs, rightObs]
  exact ⟨fun h policy x initial p seen => ⟨h policy x initial p seen, seen.2⟩,
    fun h policy x initial p seen => (h policy x initial p seen).1⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public
