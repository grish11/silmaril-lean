module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Agreement

/-! # Typed flat SSA, mutable execution, and typed reversion agree -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)} {blocks : Nat}
  {code : FiniteCFG P.Instr blocks I.exits.length I.slots} {R : Fin blocks → Ty κ}
  [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType I.context.toList
local notation "C" => AtomValues.carrier (κ := κ)

/-- The source flat program at the supplied typed input agrees with the
actual mutable runner, retaining the old payload and ordered live-out record. -/
theorem Lowered.packed_observe (M : Model (κ := κ) Events P.Instr) (a : Lowered I fields code)
    (typed : code.HasType I.context R (LiveOut.exitInterface I fields).external)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      LiveOut.observe M I fields a.source x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.packed_observe M a typed x ambient

/-- When the existing checker admits the versioned RTL at the supplied
packet profiles, the two actual typed packed programs have equal weak
trees at each input. Their internal packet types may differ. -/
theorem Lowered.packed_roundTrip (M : Model (κ := κ) Events P.Instr) (a : Lowered I fields code)
    (typed : code.HasType I.context R (LiveOut.exitInterface I fields).external)
    (recompiled : LiveOut.Admission P I fields a.source)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      region M.raw (extend ambient (encodeValue C A x)) recompiled.program.code :=
  (a.packed_observe M typed x ambient).trans (recompiled.packed_tree M x ambient).symm

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
