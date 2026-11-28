module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut

/-! # The admitted dispatcher computes the specified exit projection -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut

open CategoryTheory
open Silmaril.SSA.LambdaRTL
open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region)
open LambdaSSA.Semantics.Interaction.Typed
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot.ITree (TraceLE)

universe u v
variable {κ V K : Type (u + 1)} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} {I : Interface κ V K}
  {fields : K → List (V × Ty κ)} {source target : CFG V K P.Instr}
  [AtomValues κ] {Events : Type u → Type u}

local notation "A" => Region.packedInputType I.context.toList
local notation "B" => Region.packedExitType (List.ofFn (Interface.external (exitInterface I fields)))
local notation "C" => AtomValues.carrier (κ := κ)

/-- The existing named runner on the source with attached reads observes
the caller's projection of the original runner. -/
theorem Admission.observe_rtl (M : Model (κ := κ) Events P.Instr) (a : Admission P I fields source)
    (x : Ty.denote C A) : a.rtl.observe M x = observe M I fields source x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.observe_rtl M a x

theorem Admission.packed_tree (M : Model (κ := κ) Events P.Instr) (a : Admission P I fields source)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    region M.raw (extend ambient (encodeValue C A x)) a.program.code = observe M I fields source x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.packed_tree M a x ambient

/-- The typed packed result encodes exactly the projection of the original
named execution. The only event semantics is that of the same model. -/
theorem Admission.denote_tree (M : Model (κ := κ) Events P.Instr) (a : Admission P I fields source)
    (x : Ty.denote C A) (ambient : Env (Sigma C)) :
    ((show ModelTree Events (Ty.denote C B) from (a.program.denote M).of x) >>=
      fun b => pure (0, encodeValue C B b)) = observe M I fields source x :=
  let _ := M.instructions
  (singletonDenote_tree M.raw M.compatible a.program.typed x ambient).trans (a.packed_tree M x ambient)

/-- Compare two admitted graphs at the same exact input and projection
interface, pointwise on the actual projected mutable observations. -/
theorem satisfies_iff (M : Model (κ := κ) Events P.Instr) (a : Admission P I fields source)
    (b : Admission P I fields target) (ambient : Env (Sigma C)) :
    M.Satisfies a.program b.program ↔
      ∀ x : Ty.denote C A, TraceLE (observe M I fields source x) (observe M I fields target x) :=
  (denote_le_iff M M a.program b.program ambient).trans
    (forall_congr' fun x => by rw [a.packed_tree M x ambient, b.packed_tree M x ambient])

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut
