module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Apex.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Apex
public import Silmaril.Logic.Institution.Hets.LogicGraph

@[expose] public section

/-!
# A cocone from finite MLTT stages to full MLTT

Every judgment appears at a finite stage, and the inclusions commute with the
maps into the full institution. This constructs a cocone; a colimit universal
property and finite bounds on derivations are separate results.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Apex

open CategoryTheory Silmaril.Logic.Institution

universe u

@[simp] theorem inclusion_refl (n : ℕ) :
    inclusion.{u} (Nat.le_refl n) = Inst.CoHom.id (finiteBundled.{u} n) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Apex.inclusion_refl n

@[simp] theorem inclusion_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    inclusion.{u} (hnm.trans hmk) =
      Inst.CoHom.comp (inclusion hnm) (inclusion hmk) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Apex.inclusion_comp hnm hmk

/-- The lifted sentence translation is the original finite translation. -/
@[simp] theorem includeSentence_down {n m : ℕ} (h : n ≤ m) (j : Sentence.{u} n) :
    (includeSentence h j).down = Finite.includeSentence h j.down := rfl

/-- The apex translation retains precisely the bounded judgment. -/
@[simp] theorem toFullSentence_down {n : ℕ} (j : Sentence.{u} n) :
    (toFullSentence j).down = j.down.val := rfl

/-- The lifted finite institutions form the same natural-number-indexed family. -/
def family : ℕ ⥤ CoIns.{0, 0, u + 1, u + 1, u + 1} where
  obj n := finiteBundled.{u} n
  map h := inclusion (leOfHom h)
  map_id n := inclusion_refl n
  map_comp f g := inclusion_comp (leOfHom f) (leOfHom g)

/-- Moving to a later stage before full MLTT leaves the translation unchanged. -/
@[simp] theorem toFull_coherent {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom.comp (inclusion.{u} h) (toFull m) = toFull n :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Apex.toFull_coherent h

/-- Each successor triangle of the finite-to-full diagram commutes. -/
theorem toFull_successor (n : ℕ) :
    Inst.CoHom.comp (successor.{u} n) (toFull (n + 1)) = toFull n :=
  toFull_coherent (Nat.le_succ n)

/-- The full MLTT institution is an apex for the finite-stage diagram. -/
def cocone : Limits.Cocone family.{u} where
  pt := Institution.bundled.{u}
  ι :=
    { app := toFull
      naturality := fun _ _ h => toFull_coherent (leOfHom h) }

/-- Lifting a finite sentence changes neither its models nor its satisfaction. -/
theorem finite_satisfaction (n : ℕ) (T : (Finite.room.{u} n).Mod)
    (j : Finite.Sentence n) :
    (finiteRoom.{u} n).Sat T (ULift.up j) ↔ (Finite.room n).Sat T j := Iff.rfl

/-- Supplied finite models remain models of the lifted family. -/
theorem finite_model_nonempty (n : ℕ) [Silmaril.Logic.SetTheory.HasFiniteTower.{u} n] :
    Nonempty (finiteRoom.{u} n).Mod := Finite.model_nonempty n

/-- Restricting a full hierarchy through an intermediate stage is coherent. -/
@[simp] theorem fullModel_restrict {n m : ℕ} (h : n ≤ m) (T : SetHierarchy.{u}) :
    (T.toFiniteTower m).restrict h = T.toFiniteTower n := rfl

/-- Semantic consequence at a finite stage transports to full MLTT. -/
theorem toFull_entails {n : ℕ} {H : Set (Sentence.{u} n)} {j : Sentence.{u} n}
    (hj : (finiteRoom.{u} n).Entails H j) :
    Institution.room.Entails (toFullSentence '' H) (toFullSentence j) :=
  (toFull.{u} n).entails_map (S := Discrete.mk ()) hj

/-- A bounded sentence keeps exactly its meaning under the full-model reduct. -/
theorem toFull_satisfaction (n : ℕ) (T : SetHierarchy.{u}) (j : Sentence.{u} n) :
    (toFullSentence j).down.Valid T ↔ j.down.val.ValidIn (T.toFiniteTower n).U :=
  (EJdg.validIn_iff_valid T j.down.val).symm

/-- Each full judgment is represented at some finite stage of the diagram. -/
theorem sentence_exhaustive (j : Institution.Sentence.{u}) :
    ∃ n, ∃ jn : Sentence.{u} n, toFullSentence jn = j :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Apex.sentence_exhaustive j

namespace Hets

/-- The finite stages together with their full-universe apex. -/
inductive Node : Type
  | finite (n : ℕ)
  | full

/-- Hets edges include finite-stage inclusions and the maps into full MLTT. -/
inductive Translation : Node → Node → Type
  | inclusion {n m : ℕ} (h : n ≤ m) : Translation (.finite n) (.finite m)
  | toFull (n : ℕ) : Translation (.finite n) .full

/-- The finite-to-full cocone as a Hets logic graph. -/
def graph : LogicGraph.{0, 0, 0, 0, u + 1, u + 1, u + 1} where
  Logics := Node
  inst
    | .finite n => finiteBundled.{u} n
    | .full => Institution.bundled.{u}
  Comor := Translation
  comor
    | .inclusion h => Apex.inclusion h
    | .toFull n => Apex.toFull n
  Mor _ _ := PEmpty
  mor e := e.elim

/-- Direct and intermediate-stage Hets routes induce the same translation. -/
theorem triangle {n m : ℕ} (h : n ≤ m) :
    Inst.CoHom.comp (graph.{u}.comor (.inclusion h)) (graph.comor (.toFull m)) =
      graph.comor (.toFull n) := toFull_coherent h

end Hets

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Apex
