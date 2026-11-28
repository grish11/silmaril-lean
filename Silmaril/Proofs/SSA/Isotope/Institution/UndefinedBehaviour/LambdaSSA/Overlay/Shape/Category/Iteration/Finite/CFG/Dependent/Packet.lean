module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category (noEmptyPayload)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
open Silmaril.Isotope.LambdaSSA.Region (packedExitValue)

variable {L : List (Silmaril.Ty Empty)}

theorem unpack_pack (p : Packet L) : unpack (pack p) = p := by
  induction L with
  | nil => exact p.1.elim0
  | cons A L ih =>
    obtain ⟨i, a⟩ := p
    revert a
    refine Fin.cases ?_ (fun j => ?_) i
    · intro a
      rfl
    · intro a
      change (let p := unpack (pack (L := L) ⟨j, a⟩); (⟨p.1.succ, p.2⟩ : Packet (A :: L))) = _
      rw [ih]

theorem pack_unpack (a : Packed L) : pack (unpack a) = a := by
  induction L with
  | nil => exact (noEmptyPayload a).elim
  | cons A L ih =>
    obtain ⟨_, typed⟩ := a
    cases typed with
    | inl => rfl
    | inr typed =>
      let tail : Packed L := ⟨_, typed⟩
      exact Subtype.ext (congrArg (fun x : Packed L => Value.inr x.val) (ih tail))

theorem pack_value (p : Packet L) : (pack p).val = packedExitValue p.1 p.2.val := by
  induction L with
  | nil => exact p.1.elim0
  | cons A L ih =>
    obtain ⟨i, a⟩ := p
    revert a
    refine Fin.cases (fun _ => rfl) (fun j a => ?_) i
    exact congrArg Isotope.Value.inr (ih ⟨j, a⟩)

theorem packet_raw_injective : Function.Injective (Packet.raw (L := L)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ eq
  have index : i = j := congrArg Prod.fst eq
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext (congrArg Prod.snd eq))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
