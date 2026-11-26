module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Admission.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Admission.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Materialize.Outline.Admission

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open SSA.FiniteSum (append)

universe u v
variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {g : FiniteCFG P.Instr blocks exits.length n} {R : Fin blocks → Ty κ}
  [AtomValues κ] {Events : Type u → Type u}

local notation "ports" => numberedInterface context exits external
local notation "exitTypes" => Interface.external (LiveOut.exitInterface ports fields)
local notation "A" => Region.packedInputType context.toList
local notation "C" => AtomValues.carrier (κ := κ)

/-- The actual named runner returns the same ordered exits and live-outs
as the original graph at the supplied typed input. -/
theorem packed_observe (s : Selection g) (typed : g.HasType context R exitTypes) {left right : Ty κ}
    (arm : s.arm.HasType context (append R exitTypes) (R s.selected) left right)
    (M : Model (κ := κ) Events P.Instr)
    (c : Compiled (context := context) (external := external) (fields := fields) s)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      LiveOut.observe M ports fields c.lowered.source x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline.packed_observe s typed arm M c x ambient

/-- The same public equation holds for the actual packed reversion. -/
theorem packed_roundTrip (s : Selection g) (typed : g.HasType context R exitTypes) {left right : Ty κ}
    (arm : s.arm.HasType context (append R exitTypes) (R s.selected) left right)
    (M : Model (κ := κ) Events P.Instr)
    (c : Compiled (context := context) (external := external) (fields := fields) s)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      region M.raw (extend ambient (encodeValue C A x)) c.admission.program.code :=
  (packed_observe s typed arm M c x ambient).trans (c.admission.packed_tree M x ambient).symm

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
