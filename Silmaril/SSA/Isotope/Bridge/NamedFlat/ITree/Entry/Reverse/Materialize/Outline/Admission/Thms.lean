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

omit [DecidableEq K] in
/-- Outlining commutes with the existing packed interpretation at the same
typed record, before the checks and named reversion. -/
theorem packed_graph_tree (s : Selection g) (typed : g.HasType context R exitTypes) {left right : Ty κ}
    (arm : s.arm.HasType context (append R exitTypes) (R s.selected) left right)
    (M : Model (κ := κ) Events P.Instr)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry (graph_hasType s typed arm)).code :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline.packed_graph_tree s typed arm M x ambient

/-- The actual named runner returns the same ordered exits and live-outs
as the original graph at the supplied typed input, including through
cyclic transfers. -/
theorem checked_packed_observe (s : Selection g) (typed : g.HasType context R exitTypes) {left right : Ty κ}
    (arm : s.arm.HasType context (append R exitTypes) (R s.selected) left right)
    (M : Model (κ := κ) Events P.Instr)
    (c : Checked (context := context) (external := external) (fields := fields) s)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      LiveOut.observe M ports fields c.lowered.source x :=
  (packed_graph_tree s typed arm M x ambient).trans
    (Materialize.lowered_packed_observe (graph_hasType s typed arm) M c.lowered x ambient)

/-- The actual typed packet-local reversion satisfies the same equation
without a reachable-rank certificate. -/
theorem checked_packed_roundTrip (s : Selection g) (typed : g.HasType context R exitTypes) {left right : Ty κ}
    (arm : s.arm.HasType context (append R exitTypes) (R s.selected) left right)
    (M : Model (κ := κ) Events P.Instr)
    (c : Checked (context := context) (external := external) (fields := fields) s)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      region M.raw (extend ambient (encodeValue C A x)) c.admission.program.code :=
  (checked_packed_observe s typed arm M c x ambient).trans (c.admission.packed_tree M x ambient).symm

/-- The actual named runner returns the same ordered exits and live-outs
as the original graph at the supplied typed input. -/
theorem packed_observe (s : Selection g) (typed : g.HasType context R exitTypes) {left right : Ty κ}
    (arm : s.arm.HasType context (append R exitTypes) (R s.selected) left right)
    (M : Model (κ := κ) Events P.Instr)
    (c : Compiled (context := context) (external := external) (fields := fields) s)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      LiveOut.observe M ports fields c.lowered.source x :=
  checked_packed_observe s typed arm M ⟨c.lowered, c.admission⟩ x ambient

/-- The same public equation holds for the actual packed reversion. -/
theorem packed_roundTrip (s : Selection g) (typed : g.HasType context R exitTypes) {left right : Ty κ}
    (arm : s.arm.HasType context (append R exitTypes) (R s.selected) left right)
    (M : Model (κ := κ) Events P.Instr)
    (c : Compiled (context := context) (external := external) (fields := fields) s)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      region M.raw (extend ambient (encodeValue C A x)) c.admission.program.code :=
  checked_packed_roundTrip s typed arm M ⟨c.lowered, c.admission⟩ x ambient

/-- The two outlines compose through actual named admission at the original
caller record and selected live-outs. -/
theorem TwoArms.packed_observe (s : TwoArms g) (typed : g.HasType context R exitTypes)
    {left right left' right' : Ty κ}
    (first : s.first.arm.HasType context (append R exitTypes) (R s.first.selected) left right)
    (second : s.second.arm.HasType context (append (s.first.packetTypes R left right) exitTypes)
      (s.first.packetTypes R left right s.second.selected) left' right')
    (M : Model (κ := κ) Events P.Instr)
    (c : Compiled (context := context) (external := external) (fields := fields) s.second)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      LiveOut.observe M ports fields c.lowered.source x :=
  (packed_graph_tree s.first typed first M x ambient).trans
    (Outline.packed_observe s.second (graph_hasType s.first typed first) second M c x ambient)

/-- The packed reversion of the same double outline preserves the original
typed entry and outward observation. -/
theorem TwoArms.packed_roundTrip (s : TwoArms g) (typed : g.HasType context R exitTypes)
    {left right left' right' : Ty κ}
    (first : s.first.arm.HasType context (append R exitTypes) (R s.first.selected) left right)
    (second : s.second.arm.HasType context (append (s.first.packetTypes R left right) exitTypes)
      (s.first.packetTypes R left right s.second.selected) left' right')
    (M : Model (κ := κ) Events P.Instr)
    (c : Compiled (context := context) (external := external) (fields := fields) s.second)
    (x : Record.Input context) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      region M.raw (extend ambient (encodeValue C A x)) c.admission.program.code :=
  (s.packed_observe typed first second M c x ambient).trans (c.admission.packed_tree M x ambient).symm

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Materialize.Outline
