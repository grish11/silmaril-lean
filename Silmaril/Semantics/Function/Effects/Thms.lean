module

public import Silmaril.Semantics.Function.Effects.Defs
public import Silmaril.Semantics.Region.Semantic.Thms

@[expose] public section
namespace Silmaril.Semantics.Function.Effects
universe u v w x

theorem Problem.sound_iff {Index : Type u} {Effect : Type v} [CompleteLattice Effect]
    (problem : Problem Index Effect) (summary : Index → Effect) :
    problem.Sound summary ↔ problem.least ≤ summary :=
  ⟨fun sound index => iSup_le fun event => iSup_le fun occurs => sound index event occurs,
    fun le index event occurs =>
      (le_iSup_of_le event (le_iSup (fun _ : problem.occurs index event => problem.observe event) occurs)).trans
        (le index)⟩

theorem Problem.abstractInput_sound {Index : Type u} {Concrete : Type v} {Effect : Type w} [Preorder Effect]
    {problem : Problem Concrete Effect} {represents : Index → Concrete → Prop}
    {summary : Concrete → Effect} {bound : Index → Effect}
    (sound : problem.Sound summary) (majorizes : ∀ index input, represents index input → summary input ≤ bound index) :
    (problem.abstractInput represents).Sound bound :=
  fun index event ⟨input, rep, occurs⟩ => (sound input event occurs).trans (majorizes index input rep)

theorem sequence_mono {Input : Type u} {Middle : Type v} {Output : Type w} {Effect : Type x}
    {combine : Effect → Effect → Effect} {first first' : Summary Input Middle Effect}
    {second second' : Summary Middle Output Effect} (left : Refines first first') (right : Refines second second') :
    Refines (sequence combine first second) (sequence combine first' second') :=
  fun {_ _ _} ⟨mid, firstFx, secondFx, h₁, h₂, effect⟩ => ⟨mid, firstFx, secondFx, left h₁, right h₂, effect⟩

open Silmaril.Semantics.Region in
theorem exitSound_iff {State : Type*} {Label : Type*} {Event : Type*} {Stop : Type*}
    (machine : TransitionSystem State Label Event Stop) (support : Label → Prop)
    (admit : State → Prop) (exits : Label → List Event → State → Prop)
    (halts : Stop → List Event → State → Prop) :
    ExitSound machine support admit exits halts ↔ PartialHoare machine admit support exits halts :=
  ⟨fun h => ⟨fun s es t hs => (h s hs).1 s es t rfl, fun s es t k hs => (h s hs).2 s es t k rfl⟩,
    fun h _ hs => ⟨fun _ es t eq => eq.symm ▸ h.1 _ es t hs, fun _ es t k eq => eq.symm ▸ h.2 _ es t k hs⟩⟩

end Silmaril.Semantics.Function.Effects
