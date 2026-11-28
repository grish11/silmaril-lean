module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree (HandledTrace)

theorem combineStoreVerdicts_eq_some_iff (verdicts : List (Option Bool)) (verdict : Bool) :
    combineStoreVerdicts verdicts = some verdict ↔
      (∀ result ∈ verdicts, result.isSome = true) ∧
      (verdict = true ↔ ∀ result ∈ verdicts, result = some true) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Stores.combine_eq_some verdicts verdict

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type} [DecidableEq F]
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {leftCapture rightCapture : V} {leftType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  {count : Nat} (left : Seeded signature source exits fields leftCapture leftType outputs)
  (right : Seeded signature target exits fields rightCapture rightType outputs)
  (stores : Fin count → V → Value Atom)

/-- Missing a typed seed on either side at any supplied store gives no
verdict for the interface. -/
theorem Seeded.refinementOverStores?_eq_none_iff :
    left.refinementOverStores? right stores = none ↔
      ∃ i, left.seed? (stores i) = none ∨ right.seed? (stores i) = none :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Stores.eq_none left right stores

/-- A verdict requires typed seeds on both sides at every store. Its
Boolean decides directed handled-trace inclusion on the original runners
at every store in the supplied finite interface. -/
theorem Seeded.refinementOverStores?_eq_some_iff (verdict : Bool) :
    left.refinementOverStores? right stores = some verdict ↔
      (∀ i, (left.seed? (stores i)).isSome = true ∧ (right.seed? (stores i)).isSome = true) ∧
      (verdict = true ↔ ∀ i (policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature),
        ∀ x, policy.initial x → ∀ trace,
          HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields source (stores i)) trace →
          HandledTrace policy.step x (LiveOut.observeRaw signature.primitive exits fields target (stores i)) trace) :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Stores.eq_some left right stores verdict

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
