module

public import Silmaril.Machine.MulticoreVM.Institution.Defs
public import Silmaril.Machine.MulticoreVM.Thms
public import Silmaril.Semantics.ConcurrentTrace.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.Institution
open Silmaril.Semantics.ConcurrentTrace (Letter Word mapWord mapTrace_id mapTrace_comp)

universe u

variable {O P Q : Type u}

theorem sentenceMap_id (φ : Sentence O) : φ.map id = φ := by
  induction φ <;> simp [Sentence.map, *]

theorem sentenceMap_comp (f : O → P) (g : P → Q) (φ : Sentence O) :
    φ.map (g ∘ f) = (φ.map f).map g := by
  induction φ <;> simp [Sentence.map, *]

theorem satisfaction (f : O → P) (M : Model P) (φ : Sentence O) :
    (φ.map f).Holds M ↔ φ.Holds (reduct f M) := by
  induction φ with
  | truth | possible => rfl
  | neg _ ih => exact not_congr ih
  | conj _ _ ih₁ ih₂ => exact and_congr ih₁ ih₂
  | disj _ _ ih₁ ih₂ => exact or_congr ih₁ ih₂

variable {A B C : Sig.{u}}

private theorem letter_id (l : Letter A.ThreadId A.Event) :
    l.map (𝟙 A : A ⟶ A).thread (𝟙 A : A ⟶ A).event = l := by
  cases l with
  | event => rfl
  | sync participants => exact congrArg Letter.sync (List.map_id participants)

private theorem letter_comp (f : A ⟶ B) (g : B ⟶ C) (l : Letter A.ThreadId A.Event) :
    l.map (f ≫ g).thread (f ≫ g).event = (l.map f.thread f.event).map g.thread g.event := by
  cases l with
  | event => rfl
  | sync => exact congrArg Letter.sync (List.map_map (f := f.thread) (g := g.thread)).symm

theorem mapNamed_id (word : A.NamedWord) : Sig.Hom.mapNamed (𝟙 A) word = word := by
  unfold Sig.Hom.mapNamed mapWord
  exact (List.map_congr_left (g := id) (fun l _ => letter_id l)).trans (List.map_id word)

theorem mapNamed_comp (f : A ⟶ B) (g : B ⟶ C) (word : A.NamedWord) :
    Sig.Hom.mapNamed (f ≫ g) word = Sig.Hom.mapNamed g (Sig.Hom.mapNamed f word) := by
  unfold Sig.Hom.mapNamed mapWord
  rw [List.map_map]
  exact List.map_congr_left fun l _ => letter_comp f g l

theorem mapConcurrent_id (trace : A.ConcurrentTrace) :
    Sig.Hom.mapConcurrent (𝟙 A) trace = trace :=
  DFunLike.congr_fun mapTrace_id trace

theorem mapConcurrent_comp (f : A ⟶ B) (g : B ⟶ C) (trace : A.ConcurrentTrace) :
    Sig.Hom.mapConcurrent (f ≫ g) trace = Sig.Hom.mapConcurrent g (Sig.Hom.mapConcurrent f trace) :=
  DFunLike.congr_fun (mapTrace_comp f.thread f.thread.injective f.event
    g.thread g.thread.injective g.event).symm trace

theorem mapCore_id (word : A.CoreWord) : Sig.Hom.mapCore (𝟙 A) word = word := by
  unfold Sig.Hom.mapCore
  exact (List.map_congr_left (g := id)
    (fun p _ => congrArg (p.1, ·) (letter_id p.2))).trans (List.map_id word)

theorem mapCore_comp (f : A ⟶ B) (g : B ⟶ C) (word : A.CoreWord) :
    Sig.Hom.mapCore (f ≫ g) word = Sig.Hom.mapCore g (Sig.Hom.mapCore f word) := by
  unfold Sig.Hom.mapCore
  rw [List.map_map]
  exact List.map_congr_left fun p _ => congrArg (g.core (f.core p.1), ·) (letter_comp f g p.2)

theorem mem_ofVM_iff_run {State Thread Choice Event : Type u}
    (observe : Word Thread Event → O) (step : Transition State Thread Choice Event)
    (initial : State) (obs : O) :
    obs ∈ ofVM observe step initial ↔
      ∃ n word final, (final, word) ∈ namedOutcomes (run step n) initial ∧ observe word = obs := by
  constructor
  · rintro ⟨schedule, word, final, execution, rfl⟩
    exact ⟨schedule.length, word, final,
      (mem_run_iff_exists_schedule _).mpr ⟨schedule, rfl, execution⟩, rfl⟩
  · rintro ⟨n, word, final, execution, rfl⟩
    obtain ⟨schedule, _, scheduled⟩ := (mem_run_iff_exists_schedule n).mp execution
    exact ⟨schedule, word, final, scheduled, rfl⟩

end Silmaril.Proofs.Machine.MulticoreVM.Institution
