module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Straight.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered

universe u v

variable {κ K : Type (u + 1)} [DecidableEq K] [AtomValues κ]
  {n blocks : Nat} {P : FlatInstitution.Signature.{u, v} κ}
  {context : BoundCtx (Ty κ) n} {exits : List K} {external : Fin exits.length → Ty κ}
  {fields : K → List (Register × Ty κ)}
  {code : FiniteCFG P.Instr blocks exits.length n}

variable (a : Lowered (numberedInterface context exits external) fields code)

local notation "attached" => withLiveOut (P := P) fields a.source
local notation "C" => AtomValues.carrier (κ := κ)
local notation "Input" => Ty.denote C (Region.packedInputType context.toList)

theorem encode_captures {Events : Type u → Type u} (M : Model (κ := κ) Events P.Instr)
    (slots : List (Fin n)) (x : Input) (transfer : CFG.Cyclic.Transfer Register K (Value (Sigma C)))
    (route : CFG.Cyclic.Versioning.destinations attached transfer.1 =
      some (slots.map (fun j => (⟨j.val⟩ : Register))))
    (agrees : ∀ j ∈ slots, transfer.2.2 ⟨j.val⟩ = inputEnv context x j.val) :
    CFG.Cyclic.Versioning.encode (treeModel M.raw) attached transfer =
      (transfer.1, .pair transfer.2.1
        (slots.foldr (fun j tail => .pair (inputEnv context x j.val) tail) .unit)) := by
  have packed : Version.packVal (treeModel M.raw) transfer.2.2
      (slots.map (fun j => (⟨j.val⟩ : Register))) =
      slots.foldr (fun j tail => .pair (inputEnv context x j.val) tail) .unit := by
    clear route
    induction slots with
    | nil => rfl
    | cons j tail ih =>
      change Value.pair (transfer.2.2 ⟨j.val⟩)
        (Version.packVal (treeModel M.raw) transfer.2.2 (tail.map (fun k => (⟨k.val⟩ : Register)))) = _
      rw [agrees j (by simp), ih (fun k mem => agrees k (List.mem_cons_of_mem _ mem))]
      rfl
  simp only [CFG.Cyclic.Versioning.encode, Version.enc, route, packed]
  rfl

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Reverse.Straight
