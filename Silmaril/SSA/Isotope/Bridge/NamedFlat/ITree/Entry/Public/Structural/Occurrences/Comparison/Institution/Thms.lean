module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Occurrences.Comparison.Institution

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution

open CategoryTheory Opposite Silmaril.Logic.ITree Silmaril.Logic.Institution
open Silmaril.Elgot.ITree (TraceSignature)

instance : Category.{1} OpcodeSignature where
  Hom := OpcodeSignature.Arrow
  id := OpcodeSignature.Arrow.id
  comp := OpcodeSignature.Arrow.comp
  id_comp f := by
    exact Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.arrow_ext
      rfl (Category.id_comp f.events)
  comp_id f := by
    exact Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.arrow_ext
      rfl (Category.comp_id f.events)
  assoc f g h := by
    exact Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.arrow_ext
      rfl (Category.assoc f.events g.events h.events)

/-- Forget the opcode witnesses, retaining the existing typed trace arrow. -/
def traceSignatures : OpcodeSignature ⥤ TraceSignature.{0} where
  obj S := S.primitive.traceSignature
  map f := f.events
  map_id _ := rfl
  map_comp _ _ := rfl

universe u

variable {V K : Type 1} [DecidableEq V] [DecidableEq K]
  {S T U : OpcodeSignature} {exits : List K} {fields : K → List V}

@[simp] theorem Sentence.map_id (φ : Sentence S exits fields) : φ.map (𝟙 S) = φ :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.map_id φ

theorem Sentence.map_comp (φ : Sentence S exits fields) (f : S ⟶ T) (g : T ⟶ U) :
    φ.map (f ≫ g) = (φ.map f).map g :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.map_comp φ f g

theorem Admission.observe_original {point : Endpoints V K S} (a : Admission point exits fields) :
    a.observe = point.observe exits fields :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.observe_original a

/-- The translated trace sentence is realized by the actual mapped
occurrence admissions at the same two decoded packets. -/
theorem Admission.observe_map {point : Endpoints V K S} (a : Admission point exits fields) (f : S ⟶ T) :
    (a.map f).observe = a.observe.translate f.events :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution.observe_map a f

theorem Sentence.compile_eq_original (φ : Sentence S exits fields) : φ.compile = φ.val.observe exits fields :=
  (Classical.choice φ.property).observe_original

/-- All successful certificates for this pair of written endpoints and
store give the same occurrence sentence. -/
theorem Sentence.compile_eq_admitted (φ : Sentence S exits fields) (a : Admission φ.val exits fields) :
    φ.compile = a.observe :=
  φ.compile_eq_original.trans a.observe_original.symm

/-- The admission-aware sentence translation commutes with signature change. -/
theorem Sentence.compile_map (φ : Sentence S exits fields) (f : S ⟶ T) :
    (φ.map f).compile = φ.compile.translate f.events := by
  let a := Classical.choice φ.property
  exact ((φ.map f).compile_eq_admitted (a.map f)).trans
    ((a.observe_map f).trans (congrArg (TraceInstitution.Sentence.translate f.events) (φ.compile_eq_admitted a).symm))

/-- The existing model reduct and #4715 satisfaction law for the original
runners at a checked store. -/
theorem Sentence.sat_map_iff (φ : Sentence S exits fields) (f : S ⟶ T)
    (policy : Model.{0, u} T.primitive.traceSignature.toSignature) :
    TraceInstitution.Sat policy ((φ.map f).val.observe exits fields) ↔
      TraceInstitution.Sat (policy.reduct f.events.hom) (φ.val.observe exits fields) := by
  rw [← (φ.map f).compile_eq_original, ← φ.compile_eq_original, φ.compile_map f]
  exact TraceInstitution.satisfaction f.events policy _

variable (exits : List K) (fields : K → List V)

/-- The original RTL sentences restricted to the checked occurrence domain.
The model functor is the existing discrete reply-policy functor. -/
noncomputable def institution : ClassicInstitution.{1, 1, 2, u + 1, u + 1} OpcodeSignature where
  Sen :=
    { obj S := ULift.{2} (Sentence S exits fields)
      map f := TypeCat.ofHom fun φ => ⟨φ.down.map f⟩
      map_id _ := congrArg TypeCat.ofHom (funext fun φ => congrArg ULift.up φ.down.map_id)
      map_comp f g := congrArg TypeCat.ofHom (funext fun φ => congrArg ULift.up (φ.down.map_comp f g)) }
  Mod := traceSignatures.op ⋙ TraceInstitution.models.{0, u}
  Sat _ M φ := TraceInstitution.Sat M.as (φ.down.val.observe exits fields)
  satisfaction f M φ := φ.down.sat_map_iff f M.as

noncomputable def inst : Inst.{1, 1, 2, u + 1, u + 1} :=
  ⟨OpcodeSignature, (institution exits fields).toRoomFunctor⟩

/-- The target is the existing handled-trace institution at the chosen universes. -/
noncomputable def traceInst : Inst.{1, 1, 2, u + 1, u + 1} :=
  ⟨TraceSignature.{0}, (TraceInstitution.institution.{0, 1, u}).toRoomFunctor⟩

/-- Translate the checked original endpoints to their admitted SSA
observation sentence in the existing handled-trace institution. -/
noncomputable def comorphism :
    Inst.CoHom (inst.{u} exits fields) traceInst.{u} where
  Φ := traceSignatures
  ρ :=
    { app := fun _ => ⟨fun φ => φ.down.compile, 𝟭 _, fun M φ => by
        change TraceInstitution.Sat M.as φ.down.compile ↔ TraceInstitution.Sat M.as (φ.down.val.observe exits fields)
        rw [φ.down.compile_eq_original]⟩
      naturality := fun _ _ f => Room.hom_ext
        (funext fun φ => φ.down.compile_map f)
        (by
          change 𝟭 _ ⋙ (TraceInstitution.models.map f.events.op).toFunctor =
            (TraceInstitution.models.map f.events.op).toFunctor ⋙ 𝟭 _
          rw [Functor.id_comp, Functor.comp_id]) }

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public.OccurrenceInstitution
