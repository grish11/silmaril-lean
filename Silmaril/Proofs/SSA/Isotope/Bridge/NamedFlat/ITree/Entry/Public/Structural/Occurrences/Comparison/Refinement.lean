module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Refinement.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution

open CategoryTheory Silmaril.Logic.ITree
open Silmaril.Elgot.ITree (HandledTrace)
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution

universe u

variable {V K : Type 1} [DecidableEq V] [DecidableEq K]
  {S T : OpcodeSignature} {exits : List K} {fields : K → List V}

theorem sat_directed (point : Endpoints V K S)
    (policy : Model.{0, u} S.primitive.traceSignature.toSignature) :
    TraceInstitution.Sat policy (point.observe exits fields) ↔
      ∀ x, policy.initial x → ∀ trace,
        HandledTrace policy.step x (Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.observeRaw S.primitive.primitive
          exits fields point.left point.initial) trace →
        HandledTrace policy.step x (Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.observeRaw S.primitive.primitive
          exits fields point.right point.initial) trace := by
  exact ⟨fun sat x init trace seen => ⟨sat x init trace seen, seen.2⟩,
    fun incl x init trace seen => (incl x init trace seen).1⟩

theorem valid_map (φ : Sentence S exits fields) (f : S ⟶ T) :
    (∀ policy : Model.{0, 0} T.primitive.traceSignature.toSignature,
      TraceInstitution.Sat policy (φ.map f).compile) ↔
    (∀ policy : Model.{0, 0} S.primitive.traceSignature.toSignature,
      TraceInstitution.Sat policy φ.compile) := by
  rw [φ.compile_map f, φ.compile_eq_original, Endpoints.observe, TraceInstitution.translate_hasTrace]
  exact (TraceInstitution.valid_hasTrace_iff _ _).trans
    (f.events.traceLE_iff.trans (TraceInstitution.valid_hasTrace_iff _ _).symm)

theorem verdict_valid {point : Endpoints V K S} [DecidableEq S.Opcode] (a : Admission point exits fields) :
    a.comparison.fromStore? point.initial = some true ↔
      ∀ policy : Model.{0, 0} S.primitive.traceSignature.toSignature,
        TraceInstitution.Sat policy a.observe := by
  rw [a.comparison.fromStore?_eq_some_iff]
  constructor
  · rintro ⟨p, q, hp, hq, valid⟩
    have hp' := Option.some.inj (hp.symm.trans a.leftSeed)
    have hq' := Option.some.inj (hq.symm.trans a.rightSeed)
    subst p
    subst q
    exact valid.mp rfl
  · intro valid
    exact ⟨a.leftPacket, a.rightPacket, a.leftSeed, a.rightSeed, ⟨fun _ => valid, fun _ => rfl⟩⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution
