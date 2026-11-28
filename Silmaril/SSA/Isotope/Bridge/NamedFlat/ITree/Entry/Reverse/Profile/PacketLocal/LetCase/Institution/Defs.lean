module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Thms
public import Silmaril.SSA.Isotope.Institution.LetCase.WeakITree.Thms

/-! # The exact LetCase equation of two ranked packet-local admissions -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Acyclic.Positional
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Isotope.Institution.LetCase.WeakITree (Equation closedOperand)

universe u

variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks blocks' : Nat} {P : FlatInstitution.Signature.{u, u+1} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n} {code' : FiniteCFG P.Instr blocks' exits.length n}
  {a : Lowered (numberedInterface context exits external) fields code}
  {b : Lowered (numberedInterface context exits external) fields code'}

local notation "ports" => numberedInterface context exits external
local notation "B" => Region.packedExitType (List.ofFn (Interface.external (LiveOut.exitInterface ports fields)))

/-- Use the existing exact equation sentence with both expanded terms.
Its sort keeps the shared caller context and the ordered exit sum,
including each exit's selected live-out record. -/
noncomputable def Admission.equation (left : Admission a) (right : Admission b)
    (leftRank : left.acyclicCheck = true) (rightRank : right.acyclicCheck = true) : Equation P :=
  ⟨⟨n, context, B⟩, closedOperand (P := P) (left.letCase leftRank).2,
    closedOperand (P := P) (right.letCase rightRank).2⟩

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
