module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.PacketLocal.LetCase.Institution.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry
open _root_.Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse
open _root_.Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
open Silmaril.Isotope.LambdaSSA (FiniteCFG)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Institution.LetCase.WeakITree
open Silmaril.Isotope.Semantics (encodeValue encodeValue_injective)
open Silmaril.Elgot.ITree (eq_iff_traceLE TraceLE)
open scoped Silmaril.Elgot.ITree.WeakKleisli

universe u

variable {κ K : Type (u + 1)} [DecidableEq K]
  {n blocks blocks' : Nat} {P : FlatInstitution.Signature.{u, u+1} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n} {code' : FiniteCFG P.Instr blocks' exits.length n}
  {a : Lowered (numberedInterface context exits external) fields code}
  {b : Lowered (numberedInterface context exits external) fields code'}
  [AtomValues κ] {Events : Type u → Type u}

local notation "ports" => numberedInterface context exits external
local notation "C" => AtomValues.carrier (κ := κ)
local notation "Γ₀" => (emptyContext (κ := κ))

variable (M : Model (κ := κ) Events P.Instr) (left : Admission a) (right : Admission b)
  (leftRank : left.acyclicCheck = true) (rightRank : right.acyclicCheck = true)

theorem satisfies_iff_native :
    (equationRoom P).Sat (algebra (P := P) M) (left.equation right leftRank rightRank) ↔
      ∀ x : Record.Input context, left.letCaseTree M leftRank x = right.letCaseTree M rightRank x := by
  let l := (left.letCase leftRank).2
  let r := (right.letCase rightRank).2
  refine (Silmaril.Isotope.Institution.LetCase.sat_iff Γ₀ (signature P) (algebra (P := P) M)
    (closedOperand (P := P) l).2 (closedOperand (P := P) r).2).trans ?_
  constructor
  · intro equal x
    simpa only [denote_closedOperand, Admission.letCaseTree, l, r] using congrFun equal (Record.field context x)
  · intro equal
    funext env
    obtain ⟨x, rfl⟩ := Record.field_surjective context env
    simpa only [denote_closedOperand, Admission.letCaseTree, l, r] using equal x

private theorem retag_eq_iff {A : Ty κ} {X Y : ModelTree Events (Ty.denote C A)} :
    (X >>= fun b => pure (0, encodeValue C A b)) =
      (Y >>= fun b => pure (0, encodeValue C A b)) ↔ X = Y := by
  let tag := fun b => ((0 : Nat), encodeValue C A b)
  have injective : Function.Injective tag :=
    fun _ _ eq => encodeValue_injective C A (congrArg Prod.snd eq)
  change (X >>= fun b => pure (tag b)) = (Y >>= fun b => pure (tag b)) ↔ X = Y
  rw [eq_iff_traceLE, eq_iff_traceLE (t := X), TraceLE.bind_pure_iff injective,
    TraceLE.bind_pure_iff injective]

theorem satisfies_iff_named :
    (equationRoom P).Sat (algebra (P := P) M) (left.equation right leftRank rightRank) ↔
      ∀ x : Record.Input context, LiveOut.observe M ports fields a.source x =
        LiveOut.observe M ports fields b.source x := by
  rw [satisfies_iff_native M left right leftRank rightRank]
  apply forall_congr'
  intro x
  let ambient : Env (Sigma C) := fun _ => .unit
  rw [← left.letCase_observe M leftRank x ambient, ← right.letCase_observe M rightRank x ambient]
  exact retag_eq_iff.symm

theorem packed_eq_iff_named :
    left.program.denote M = right.program.denote M ↔
      ∀ x : Record.Input context, LiveOut.observe M ports fields a.source x =
        LiveOut.observe M ports fields b.source x := by
  let ambient : Env (Sigma C) := fun _ => .unit
  rw [le_antisymm_iff, denote_le_iff M M _ _ ambient, denote_le_iff M M _ _ ambient]
  simp only [Admission.packed_tree]
  rw [← forall_and]
  exact forall_congr' (fun _ => eq_iff_traceLE.symm)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.PacketLocal
