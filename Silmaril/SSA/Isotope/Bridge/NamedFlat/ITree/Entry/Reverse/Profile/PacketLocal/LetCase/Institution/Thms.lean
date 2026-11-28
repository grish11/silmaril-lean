module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocalLetCaseInstitution

/-! # Satisfaction of the exact equation at the shared public interface -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

open CategoryTheory
open LambdaSSA (FiniteCFG)
open LambdaSSA.Acyclic.Positional
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Isotope.Institution.LetCase.WeakITree

universe u

variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks blocks' : Nat} {P Q : FlatInstitution.Signature.{u, u+1} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n} {code' : FiniteCFG P.Instr blocks' exits.length n}
  {a : Lowered (numberedInterface context exits external) fields code}
  {b : Lowered (numberedInterface context exits external) fields code'}
  [AtomValues κ] {Events : Type u → Type u}

local notation "ports" => numberedInterface context exits external
local notation "Γ₀" => (emptyContext (κ := κ))

variable (M : Model (κ := κ) Events P.Instr) (left : Admission a) (right : Admission b)
  (leftRank : left.acyclicCheck = true) (rightRank : right.acyclicCheck = true)

/-- Institutional satisfaction is equality of the native LetCase trees at
every typed caller record. -/
theorem Admission.satisfies_iff_native :
    (equationRoom P).Sat (algebra (P := P) M) (left.equation right leftRank rightRank) ↔
      ∀ x : Record.Input context, left.letCaseTree M leftRank x = right.letCaseTree M rightRank x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.satisfies_iff_native M left right leftRank rightRank

/-- The same equation is satisfied exactly when the named runners agree
on weak trees at every caller record, retaining ordered exits and live-outs. -/
theorem Admission.satisfies_iff_named :
    (equationRoom P).Sat (algebra (P := P) M) (left.equation right leftRank rightRank) ↔
      ∀ x : Record.Input context, LiveOut.observe M ports fields a.source x =
        LiveOut.observe M ports fields b.source x :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.satisfies_iff_named M left right leftRank rightRank

/-- Equations compare the existing typed packed denotations at the same
input and tagged output types. -/
theorem Admission.satisfies_iff_packed :
    (equationRoom P).Sat (algebra (P := P) M) (left.equation right leftRank rightRank) ↔
      left.program.denote M = right.program.denote M :=
  (Admission.satisfies_iff_named M left right leftRank rightRank).trans
    (Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal.packed_eq_iff_named M left right).symm

/-- Translate the actual LetCase equation using the institution's sentence
map. Comparing the original named runners then uses its primitive reduct. -/
theorem Admission.satisfies_map_iff_named (g : P ⟶ Q) (effects : g.toSignatureMap.eff = id)
    (N : Model (κ := κ) Events Q.Instr) :
    ((Isotope.Institution.LetCase.inst Γ₀).obj (signature Q)).Sat (algebra (P := Q) N)
      (((Isotope.Institution.LetCase.inst Γ₀).map (signatureHom g effects)).sen
        (left.equation right leftRank rightRank)) ↔
      ∀ x : Record.Input context,
        LiveOut.observe (FlatInstitution.reduct Events g N) ports fields a.source x =
        LiveOut.observe (FlatInstitution.reduct Events g N) ports fields b.source x :=
  (satisfaction g effects N _).trans
    (Admission.satisfies_iff_named (FlatInstitution.reduct Events g N) left right leftRank rightRank)

/-- Under the same relabelling, the translated equation also compares the
existing packed programs with their written primitives relabelled. -/
theorem Admission.satisfies_map_iff_packed (g : P ⟶ Q) (effects : g.toSignatureMap.eff = id)
    (N : Model (κ := κ) Events Q.Instr) :
    ((Isotope.Institution.LetCase.inst Γ₀).obj (signature Q)).Sat (algebra (P := Q) N)
      (((Isotope.Institution.LetCase.inst Γ₀).map (signatureHom g effects)).sen
        (left.equation right leftRank rightRank)) ↔
      (left.program.map g.toSignatureMap g.types).denote N =
        (right.program.map g.toSignatureMap g.types).denote N :=
  (satisfaction g effects N _).trans (by
    simpa only [FlatInstitution.reduct, denote_reduct N g.toSignatureMap g.types g.bottom] using
      Admission.satisfies_iff_packed (FlatInstitution.reduct Events g N) left right leftRank rightRank)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
