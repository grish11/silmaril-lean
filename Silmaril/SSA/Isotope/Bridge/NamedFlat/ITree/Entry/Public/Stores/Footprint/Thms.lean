module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Footprint.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Footprint

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree (HandledTrace)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type}
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {leftCapture rightCapture : V} {leftType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : Seeded signature source exits fields leftCapture leftType outputs)
  (right : Seeded signature target exits fields rightCapture rightType outputs)

theorem Seeded.seed?_eq_of_capture_agree {initial other : V → Value Atom}
    (agree : ∀ v ∈ left.initialCaptures, initial v = other v) :
    left.seed? initial = left.seed? other :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Footprint.seed_congr left agree

/-- Capture agreement fixes the actual named-runner observation,
including selected live-outs. The checked attached rows access those
values through their incoming packet and local binders. -/
theorem Seeded.observe_eq_of_capture_agree {initial other : V → Value Atom}
    (agree : ∀ v ∈ left.initialCaptures, initial v = other v)
    (typed : (left.seed? initial).isSome = true) :
    LiveOut.observeRaw signature.primitive exits fields source initial =
      LiveOut.observeRaw signature.primitive exits fields source other :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Footprint.observe_congr left agree typed

/-- Every common store whose two seeds decode has an enumerated
representative agreeing on the union of the actual capture reads. -/
theorem Seeded.footprintStores_cover (leftSupported : left.LiteralOrClosed) (rightSupported : right.LiteralOrClosed)
    (original : V → Value Atom) (typedLeft : (left.seed? original).isSome = true)
    (typedRight : (right.seed? original).isSome = true) :
    ∃ initial ∈ left.footprintStores right,
      ∀ v ∈ left.initialCaptures ∪ right.initialCaptures, initial v = original v :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Footprint.covers left right
    leftSupported rightSupported original typedLeft typedRight

/-- A verdict exists for every pair in the supported seed fragment,
including an empty joint typed-store domain. -/
theorem Seeded.refinementOverCaptures?_eq_none_iff [DecidableEq F] :
    left.refinementOverCaptures? right = none ↔ ¬ (left.LiteralOrClosed ∧ right.LiteralOrClosed) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Footprint.eq_none left right

/-- Directed refinement on the original runners is decided at every total
store that supplies both checked seed types. Registers outside the joint
capture footprint may vary freely. -/
theorem Seeded.refinementOverCaptures?_eq_some_iff [DecidableEq F] (verdict : Bool) :
    left.refinementOverCaptures? right = some verdict ↔
      left.LiteralOrClosed ∧ right.LiteralOrClosed ∧
      (verdict = true ↔
        ∀ initial, (left.seed? initial).isSome = true → (right.seed? initial).isSome = true →
          ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
            ∀ x, policy.initial x → ∀ trace,
              HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields source initial) trace →
              HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields target initial) trace) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Footprint.eq_some left right verdict

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
