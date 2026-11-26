module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Defs
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Entry Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open Silmaril.SSA.LambdaRTL
open Silmaril.Elgot
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)

universe u v w

variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)} {blocks : Nat}
  {code : FiniteCFG P.Instr blocks I.exits.length I.slots} {R : Fin blocks → Ty κ}
  [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType I.context.toList
local notation "C" => AtomValues.carrier (κ := κ)

theorem packed_observe (M : Model (κ := κ) Events P.Instr) (a : Lowered I fields code)
    (typed : code.HasType I.context R (LiveOut.exitInterface I fields).external)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code =
      LiveOut.observe M I fields a.source x := by
  let attached := withLiveOut (P := P) fields a.source
  let checked : SSA P (LiveOut.exitInterface I fields) :=
    ⟨attached, .ofTyped typed, a.count, a.readback⟩
  change region M.raw (extend ambient (encodeValue C A x)) (Program.ofCFGEntry typed).code = _
  refine (SSA.observe_tree M checked x ambient).symm.trans ?_
  have run := CFG.Cyclic.RoundTrip.run_packetClosed_obs (treeModel M.raw) attached a.closed (store I.names I.context x)
  change (CFG.Cyclic.runSSA (treeModel M.raw) attached (store I.names I.context x) >>= _) = _
  rw [← run]
  change ((obs <$> CFG.Cyclic.run (treeModel M.raw)
    (CFG.Cyclic.LiveOut.attach (fun k => (fields k).map Prod.fst) a.source)
    (store I.names I.context x)) >>= _) = _
  rw [CFG.Cyclic.LiveOut.run_project]
  simp only [LiveOut.observe, LiveOut.observeRaw, map_eq_pure_bind, bind_assoc, pure_bind]
  rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse
