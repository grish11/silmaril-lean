module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Refinement.Thms
public import Silmaril.Logic.ITree.Institution.Trace.Policy.Thms

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.ITree
open Silmaril.Elgot.ITree (TraceSignature)
open TraceInstitution (Policy)

universe u

variable {V K : Type 1} [DecidableEq V] [DecidableEq K]
  (exits : List K) (fields : K → List V) (X : Type u) (initial : X → Prop)

/-- The checked original sentence action with reply policies ordered by
allowed transitions on a fixed state carrier and initial-state predicate. -/
noncomputable def policyInstitution : ClassicInstitution.{1, 1, 2, max 1 u, max 1 u} OpcodeSignature where
  Sen := (institution.{0} exits fields).Sen
  Mod := traceSignatures.op ⋙ TraceInstitution.policyModels X
  Sat _ policy φ := TraceInstitution.Sat (Policy.toModel initial policy) (φ.down.val.observe exits fields)
  satisfaction f policy φ := φ.down.sat_map_iff f (Policy.toModel initial policy)

noncomputable def policyInst : Inst.{1, 1, 2, max 1 u, max 1 u} :=
  ⟨OpcodeSignature, (policyInstitution exits fields X initial).toRoomFunctor⟩

/-- The model component is the identity functor on each policy poset.
The original and compiled sentences have the same satisfaction predicate
for each such policy. -/
noncomputable def policyComorphism :
    Inst.CoHom (policyInst exits fields X initial)
      ⟨TraceSignature.{0}, (TraceInstitution.policyInstitution X initial).toRoomFunctor⟩ where
  Φ := traceSignatures
  ρ :=
    { app := fun _ => ⟨fun φ => φ.down.compile, 𝟭 _, fun policy φ =>
        iff_of_eq (congrArg (TraceInstitution.Sat (Policy.toModel initial policy))
          φ.down.compile_eq_original)⟩
      naturality := fun _ _ f => Room.hom_ext
        (funext fun φ => φ.down.compile_map f)
        (by
          change 𝟭 _ ⋙ (TraceInstitution.policyModels X |>.map f.events.op).toFunctor =
            (TraceInstitution.policyModels X |>.map f.events.op).toFunctor ⋙ 𝟭 _
          rw [Functor.id_comp, Functor.comp_id]) }

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution
