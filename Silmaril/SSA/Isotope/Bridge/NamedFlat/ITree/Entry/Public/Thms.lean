module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Conservativity.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (region)
open Silmaril.Elgot.ITree (HandledTrace)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {a b : Nat} {inputs : Fin a → PacketType}
  {outputs : Fin b → PacketType} {left right : Program signature inputs outputs} {input : Fin a}
  {source target : CFG V K F} {exits : List K} {fields : K → List V}

/-- Exact ordinary elaboration of the attached packet-closed graph
computes the projected observations of the original mutable runner. -/
theorem observeRaw_eq_flat {n : Nat} (names : Fin n → V)
    {flat : FiniteCFG F (LiveOut.attach fields source).blocks.length exits.length n}
    (closed : RoundTrip.PacketClosed (LiveOut.attach fields source))
    (accepted : NamedFlat.elaborate (LiveOut.attach fields source) exits names = some flat)
    (initial : V → Value Atom) (record : Env Atom)
    (captures : ∀ i, record i.val = initial (names i)) :
    Entry.LiveOut.observeRaw signature.primitive exits fields source initial =
      (region signature.primitive record flat.erase >>= fun out => pure (FiniteCFG.packedTreeOutput out)) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.observeRaw_eq_flat signature source exits fields names
    closed accepted initial record captures

/-- Exact readback and capture agreement transfer the complete weak tree
to the original mutable runner and its selected live-out observation. -/
theorem Readback.observe_eq {entry : Program.PackedEntry left input} (readback : Readback entry source exits fields)
    (initial : V → Value Atom) (ambient record : Env Atom)
    (captures : ∀ i, record i.val = initial (readback.captures i)) :
    entry.observe ambient record = Entry.LiveOut.observeRaw signature.primitive exits fields source initial :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.observe_eq entry readback initial ambient record captures

/-- Observation equations at the same packet transfer the existing
packed verdict to the original named runners. -/
theorem refinementAt?_iff_namedHandledTrace_of_observe_eq [DecidableEq F] (packet : Denote (inputs input))
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
          HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields target initial) p :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.refinementAt_namedHandledTrace_of_observe_eq packet
    leftEntry rightEntry initial leftAmbient rightAmbient leftRecord rightRecord leftObs rightObs leftAgrees rightAgrees

/-- The existing pointwise checker decides handled-trace inclusion on
the original named RTL pair at the same finite packet and initial store. -/
theorem refinementAt?_iff_namedHandledTrace [DecidableEq F] (packet : Denote (inputs input))
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
          HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields target initial) p :=
  refinementAt?_iff_namedHandledTrace_of_observe_eq packet leftEntry rightEntry initial
    leftAmbient rightAmbient leftRecord rightRecord (l.observe_eq initial leftAmbient leftRecord leftCaptures)
    (r.observe_eq initial rightAmbient rightRecord rightCaptures) leftAgrees rightAgrees

/-- Decide the original runners' comparison on the common finite public
interface. Each checked entry has matching named captures for its supplied
public packet. The original stores are supplied explicitly. -/
theorem refinement?_iff_namedHandledTrace [DecidableEq F]
    (leftEntry : ∀ input, Program.PackedEntry left input)
    (rightEntry : ∀ input, Program.PackedEntry right input)
    (l : ∀ input, Readback (leftEntry input) source exits fields)
    (r : ∀ input, Readback (rightEntry input) target exits fields)
    (initial : ∀ input, Denote (inputs input) → V → Value Atom)
    (leftAmbient rightAmbient : Env Atom)
    (leftRecord rightRecord : ∀ input, Denote (inputs input) → Env Atom)
    (leftCaptures : ∀ input packet i, leftRecord input packet i.val = initial input packet ((l input).captures i))
    (rightCaptures : ∀ input packet i, rightRecord input packet i.val = initial input packet ((r input).captures i))
    (leftAgrees : ∀ input packet, (leftEntry input).recordAgrees packet (leftRecord input packet))
    (rightAgrees : ∀ input packet, (rightEntry input).recordAgrees packet (rightRecord input packet)) :
    left.refinement? right = true ↔ ∀ input packet,
      ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
        ∀ x, policy.initial x → ∀ p,
          HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields source (initial input packet)) p →
          HandledTrace policy.step x (Entry.LiveOut.observeRaw signature.primitive exits fields target (initial input packet)) p := by
  rw [Program.refinement?, decide_eq_true_eq]
  exact forall_congr' fun input => forall_congr' fun packet =>
    refinementAt?_iff_namedHandledTrace packet (leftEntry input) (rightEntry input) (l input) (r input)
      (initial input packet) leftAmbient rightAmbient (leftRecord input packet) (rightRecord input packet)
      (leftCaptures input packet) (rightCaptures input packet) (leftAgrees input packet) (rightAgrees input packet)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
