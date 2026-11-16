module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Institution.Defs
import Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityInstitution

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Institution

open CategoryTheory Silmaril.Logic.Institution

@[ext] theorem Map.ext {S T : Signature} {F G : Map S T} (h : F.terms = G.terms) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Independently formed source LF signatures and typed interpretations form a category. -/
instance : Category Signature where
  Hom := Map
  id := Map.identity
  comp := Map.comp
  id_comp F := by apply Map.ext; rfl
  comp_id F := by apply Map.ext; funext i; exact IntensionalMLTT.Term.subst_var (F.terms i)
  assoc F G H := by
    apply Map.ext
    funext i
    exact IntensionalMLTT.Term.subst_comp (F.terms i) G.terms H.terms

/-- Reduce a target substitution model by precomposing its interpretation. -/
def Map.reduce {S T : Signature} (F : S ⟶ T) (M : Model T) : Model S :=
  ⟨M.target, F ≫ M.assignment⟩

/-- Substitution composition proves exact satisfaction under every source map. -/
theorem Map.satisfaction {S T : Signature} (F : S ⟶ T) (M : Model T) (q : Sentence S) :
    M.Satisfies (F.sentence q) ↔ (F.reduce M).Satisfies q :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityInstitution.satisfaction F M q

def corridor {S T : Signature} (F : S ⟶ T) : room S ⟶ room T where
  sen := F.sentence
  mod := Discrete.functor (fun M => Discrete.mk (F.reduce M))
  sat M q := F.satisfaction M.as q

@[ext] theorem Sentence.ext {S : Signature} {q r : Sentence S}
    (hl : q.left = r.left) (hr : q.right = r.right) (hc : q.carrier = r.carrier) : q = r := by
  cases q
  cases r
  cases hl
  cases hr
  cases hc
  rfl

/-- Source signature maps act on equality assertions and typed substitution models. -/
def institution : Signature ⥤ Room.{0, 0, 0} where
  obj := room
  map := corridor
  map_id S := by
    apply Room.hom_ext
    · funext q
      apply Sentence.ext <;> exact IntensionalMLTT.Term.subst_var _
    · apply Discrete.functor_ext
      intro M
      rfl
  map_comp F G := by
    apply Room.hom_ext
    · funext q
      apply Sentence.ext <;> exact (IntensionalMLTT.Term.subst_comp _ F.terms G.terms).symm
    · apply Discrete.functor_ext
      intro M
      change Discrete.mk ((F ≫ G).reduce M) = Discrete.mk (F.reduce (G.reduce M))
      apply congrArg Discrete.mk
      change Model.mk M.target ((F ≫ G) ≫ M.assignment) =
        Model.mk M.target (F ≫ G ≫ M.assignment)
      rw [Category.assoc]

/-- Source LF as one institution whose signatures are independently formed telescopes. -/
def bundled : Inst.{0, 0, 0, 0, 0} := ⟨Signature, institution⟩

/-- Each source signature also yields a fixed-signature institution, functorially. -/
noncomputable def institutions : Signature ⥤ CoIns.{0, 0, 0, 0, 0} :=
  institution ⋙ Silmaril.Logic.Institution.Syntactic.roomsToInstitutions

/-- Typed source interpretations become Hets comorphism edges. -/
noncomputable def hets : LogicGraph.{0, 0, 0, 0, 0, 0, 0} :=
  IndexedCoInst.toLogicGraph institutions

/-- Every source proof is true under every actual typed source interpretation. -/
theorem sound {S : Signature} (q : Sentence S)
    (h : Equality S.context S.context q.left q.right q.carrier) (M : Model S) :
    (room S).Sat (Discrete.mk M) q :=
  Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityInstitution.sound q h M

/-- The identity interpretation detects precisely the source equality judgment.
This completeness theorem concerns the syntactic substitution models above. -/
theorem valid_iff {S : Signature} (q : Sentence S) :
    (∀ M : Model S, (room S).Sat (Discrete.mk M) q) ↔
      Equality S.context S.context q.left q.right q.carrier :=
  ⟨Silmaril.Proofs.Logic.TypeTheory.LambdaPi.TypedEqualityInstitution.complete q,
    fun h M => sound q h M⟩

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.Institution
