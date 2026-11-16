module

public import Silmaril.Logic.Temporal.CTLStar.Terminal.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.Terminal.Examples
open PathFormula

abbrev sig : Signature := ⟨Unit⟩
def singletonModel : Model sig := ⟨⟨Unit, fun _ _ => False, fun _ _ => True, ()⟩⟩
def singletonPath : Path singletonModel.toModal.accessible :=
  ⟨fun _ => (), some 0, fun _ h => by simp only [ValidIndex] at h; omega,
    fun _ _ _ => id⟩

theorem singleton_not_next :
    ¬ (PathFormula.next (PathFormula.top : PathFormula sig)).Holds singletonModel singletonPath 0 :=
  next_at_terminal singletonModel _ singletonPath rfl

/-- Even weak next bottom holds at the endpoint: no next position must satisfy it. -/
theorem singleton_weakNext_bottom :
    (weakNext (.state .bot : PathFormula sig)).Holds singletonModel singletonPath 0 :=
  weakNext_at_terminal singletonModel _ singletonPath rfl

theorem singleton_until_postponement_fails :
    ¬ (PathFormula.until .top (.state .bot : PathFormula sig)).Holds singletonModel singletonPath 0 := by
  rw [until_at_terminal singletonModel _ _ singletonPath rfl]
  exact id

theorem singleton_release_without_left :
    (release (.state .bot : PathFormula sig) .top).Holds singletonModel singletonPath 0 :=
  (release_at_terminal singletonModel _ _ singletonPath rfl).mpr not_false

/-- The only edge is false → true; true is a genuine deadlock. -/
def edgeModel : Model sig :=
  ⟨⟨Bool, fun u v => u = false ∧ v = true, fun _ v => v = true, false⟩⟩
def edgePath : Path edgeModel.toModal.accessible where
  state i := if i = 0 then false else true
  last := some 1
  edges := by
    intro i hi
    have hz : i = 0 := by simp only [ValidIndex] at hi; omega
    subst i
    exact ⟨rfl, rfl⟩
  terminal := by
    intro n hn v hv
    have hn' : n = 1 := Option.some.inj hn.symm
    subst n
    exact Bool.noConfusion hv.1

theorem edge_next_atom :
    (PathFormula.next (.state (.atom ()))).Holds edgeModel edgePath 0 :=
  ⟨by change 1 ≤ 1; exact le_rfl, rfl⟩

/-- A second next step cannot use the padding beyond the last index. -/
theorem edge_not_next_next_top :
    ¬ (PathFormula.next (PathFormula.next (PathFormula.top : PathFormula sig))).Holds
      edgeModel edgePath 0 := by
  intro h
  exact next_at_terminal edgeModel _ edgePath rfl h.2

theorem edge_next_weakNext_bottom :
    (PathFormula.next (weakNext (.state .bot : PathFormula sig))).Holds edgeModel edgePath 0 :=
  ⟨by change 1 ≤ 1; exact le_rfl, weakNext_at_terminal edgeModel _ edgePath rfl⟩

end Silmaril.Logic.Temporal.CTLStar.Terminal.Examples
