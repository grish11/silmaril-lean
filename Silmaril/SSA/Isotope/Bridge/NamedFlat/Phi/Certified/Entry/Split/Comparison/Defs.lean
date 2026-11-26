module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Split.Extended.Defs

/-! # Compare admitted entries along a checked input projection -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry

open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Record (Input reindex)

universe u v

variable {κ V W K J : Type (u + 1)} {n m : Nat} {β : BoundCtx (Ty κ) n} {γ : BoundCtx (Ty κ) m}
  {I : Captures V β} {L : Captures W γ} {D : Fin 1 → Ty κ}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ}

local notation "C" => AtomValues.carrier (κ := κ)

/-- A type-preserving slot map and an observation law on every supplied
target record. A target record provides the fields used by the projection. -/
structure EntryComparison (Events : Type u → Type u)
    (original : Admitted P I K D) (target : Admitted P L J D) where
  slots : BoundCtx.Renaming β γ
  packed (M : Model (κ := κ) Events P.Instr) (record : Input γ) (ambient : Env (Sigma C)) :
    original.observePacked M (reindex slots record) ambient = target.observePacked M record ambient

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry
