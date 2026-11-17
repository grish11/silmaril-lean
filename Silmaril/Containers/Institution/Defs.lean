module

public import Silmaril.Containers.Behaviour.Defs
public import Silmaril.Logic.Institution.Basic
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# The behaviour institution of containers

The specifications of `Silmaril.Containers.Behaviour` form an institution in the sense of Goguen
and Burstall (1992), presented as a functor into rooms as in `Silmaril.Servers.Core` and
`Silmaril.Cli.Institution`:

| Notion | Lean | Reading |
| --- | --- | --- |
| signature | `Sig` (`Ev`) | the events a process is observed through |
| morphism `A ⟶ B` | `Hom` (`ev : B.Ev → A.Ev`) | what the coarser view `A` sees of each event of `B` |
| sentence | `Spec A.Ev` | a property of runs (safety, partial or total correctness, under assumptions) |
| model | `IModel A` (`Run : Beh A.Ev → Prop`) | the runs of a container under a runtime model |
| satisfaction | `IModel.Sat` | every run satisfies the sentence |

Sentences translate forwards (`Hom.sen`), models reduce backwards (`Hom.mod`, renaming the events
of every run), and the satisfaction condition holds (`Hom.sat_sen_iff`). Models are ordered by
inclusion of runs, the refinement of `Model.Refines`, which reducts preserve.

**Scope.** Morphisms rename events; they do not hide them. Hiding events is not a reduct of
this institution: a run with infinitely many hidden events becomes a silently diverging one, so
hiding changes which runs diverge. It is planned as a separate construction
(docs/projects/containers.md).

**Tables.** The parts of this institution that are data (signatures as event alphabets, profiles,
image shapes, fixtures with their runtime model and their proved sentences) are the rows the
project registry records; `Silmaril.LogicGraph.Nodes.Containers` registers its room.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Inst

open CategoryTheory Silmaril.Logic.Institution Silmaril.Containers

/-- **A signature**: an event alphabet. -/
structure Sig : Type 1 where
  Ev : Type

/-- **A model**: a set of runs. -/
@[ext] structure IModel (A : Sig) : Type where
  Run : Beh A.Ev → Prop

instance (A : Sig) : PartialOrder (IModel A) :=
  PartialOrder.lift IModel.Run fun _ _ h => IModel.ext h

/-- **Satisfaction**: every run satisfies the sentence. -/
def IModel.Sat {A : Sig} (M : IModel A) (φ : Spec A.Ev) : Prop := ∀ b, M.Run b → φ b

/-- **A morphism** `A ⟶ B`: what `A` sees of each event of `B`. -/
structure Hom (A B : Sig) : Type where
  ev : B.Ev → A.Ev

namespace Hom

variable {A B C : Sig}

def id (A : Sig) : Hom A A := ⟨_root_.id⟩

def comp (f : Hom A B) (g : Hom B C) : Hom A C := ⟨f.ev ∘ g.ev⟩

/-- **Sentence translation.** -/
def sen (h : Hom A B) (φ : Spec A.Ev) : Spec B.Ev := fun b => φ (b.map h.ev)

/-- **The reduct of a model**: its runs, with events renamed. -/
def mod (h : Hom A B) (M : IModel B) : IModel A := ⟨fun a => ∃ b, M.Run b ∧ b.map h.ev = a⟩

theorem sat_sen_iff (h : Hom A B) (M : IModel B) (φ : Spec A.Ev) :
    M.Sat (h.sen φ) ↔ (h.mod M).Sat φ :=
  ⟨fun H _ ⟨b, hb, he⟩ => he ▸ H b hb, fun H b hb => H _ ⟨b, hb, rfl⟩⟩

theorem mod_mono (h : Hom A B) {M N : IModel B} (hMN : M ≤ N) : h.mod M ≤ h.mod N :=
  fun _ ⟨b, hb, he⟩ => ⟨b, hMN b hb, he⟩

end Hom

theorem _root_.Silmaril.Containers.Beh.map_id {E : Type} (b : Beh E) : b.map _root_.id = b := by
  cases b <;> simp [Beh.map]

theorem _root_.Silmaril.Containers.Beh.map_map {E F G : Type} (f : F → G) (g : E → F)
    (b : Beh E) : (b.map g).map f = b.map (f ∘ g) := by
  cases b <;> simp [Beh.map]
  rfl

instance : Category Sig where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- The room of a signature. -/
def room (A : Sig) : Room.{0, 0, 0} := ⟨Spec A.Ev, Cat.of (IModel A), fun M φ => M.Sat φ⟩

/-- The corridor of a morphism. -/
def corridor {A B : Sig} (h : A ⟶ B) : room A ⟶ room B :=
  ⟨Hom.sen h, (Monotone.functor (f := Hom.mod h) fun _ _ hMN => Hom.mod_mono h hMN :
    IModel B ⥤ IModel A), fun M φ => Hom.sat_sen_iff h M φ⟩

theorem Hom.sen_id (A : Sig) : Hom.sen (𝟙 A) = _root_.id := by
  funext φ b; exact congrArg φ (Beh.map_id b)

theorem Hom.sen_comp {A B C : Sig} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.sen (f ≫ g) = Hom.sen g ∘ Hom.sen f := by
  funext φ b; exact congrArg φ (Beh.map_map f.ev g.ev b).symm

theorem Hom.mod_id (A : Sig) (M : IModel A) : Hom.mod (𝟙 A) M = M := by
  apply IModel.ext; funext a; apply propext
  exact ⟨fun ⟨b, hb, he⟩ => by rw [← he]; exact (Beh.map_id b).symm ▸ hb,
    fun ha => ⟨a, ha, Beh.map_id a⟩⟩

theorem Hom.mod_comp {A B C : Sig} (f : A ⟶ B) (g : B ⟶ C) (M : IModel C) :
    Hom.mod (f ≫ g) M = Hom.mod f (Hom.mod g M) := by
  apply IModel.ext; funext a; apply propext
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.map g.ev, ⟨b, hb, rfl⟩, Beh.map_map f.ev g.ev b⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, (Beh.map_map f.ev g.ev b).symm⟩

/-- **The behaviour institution of containers**, as a functor into rooms. -/
def inst : Sig ⥤ Room.{0, 0, 0} where
  obj := room
  map h := corridor h
  map_id A := Room.hom_ext (Hom.sen_id A)
    (CategoryTheory.Functor.ext (fun M => Hom.mod_id A M) (fun _ _ _ => rfl))
  map_comp f g := Room.hom_ext (Hom.sen_comp f g)
    (CategoryTheory.Functor.ext (fun M => Hom.mod_comp f g M) (fun _ _ _ => rfl))

/-- The institution in the classic presentation. -/
def classic : ClassicInstitution.{1, 0, 0, 0, 0} Sig := ClassicInstitution.ofRoomFunctor inst

/-- The institution, bundled with its category of signatures (for the logic graph). -/
def bundled : Silmaril.Logic.Institution.Inst := ⟨Sig, inst⟩

/-- The signature of the events of `Silmaril.Containers.Env`. -/
def envSig : Sig := ⟨Ev⟩

/-- The model of an image under a runtime model, at the signature of its events. -/
def ofModel {E : Type} (M : Model E) : IModel ⟨E⟩ := ⟨M⟩

end Silmaril.Containers.Inst
