module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Construction.Defs

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

/-- Keep a missing store verdict distinct from a failed comparison on a
well-typed table. -/
def combineStoreVerdicts (verdicts : List (Option Bool)) : Option Bool :=
  if verdicts.all Option.isSome then some (verdicts.all (· == some true)) else none

/-- The domain is exactly the image of the supplied store table. Each
index gives one total initial store used by both original runners.
An ill-typed seed anywhere leaves the domain without a verdict. For a
well-typed domain the verdict requires inclusion at every index. -/
def Seeded.refinementOverStores? {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type} [DecidableEq F]
    {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
    {leftCapture rightCapture : V} {leftType rightType : PacketType} {outputs : Fin exits.length → PacketType}
    {count : Nat} (left : Seeded signature source exits fields leftCapture leftType outputs)
    (right : Seeded signature target exits fields rightCapture rightType outputs)
    (stores : Fin count → V → Value Atom) : Option Bool :=
  combineStoreVerdicts (List.ofFn fun i => left.refinementFromStore? right (stores i))

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
