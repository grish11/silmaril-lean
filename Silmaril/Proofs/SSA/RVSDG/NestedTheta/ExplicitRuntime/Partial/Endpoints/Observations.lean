module

public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Transport
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Proofs

open OrderedRuntime.Structured

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}
variable (m : Model.{u,v,w} P E σ)
variable {a : Data args} {b : Data outs}
variable (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs))
variable (checked : EntryChecked (a := a) (b := b) g.toTerm)
variable (input : Tuple (RuntimeValues m.value σ) (Threaded args))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem returns_iff (output : Tuple (RuntimeValues m.value σ) (Threaded outs)) :
    NestedTheta.Partial.returns (wireModel m) g input output ↔
      boundaryResult output ∈ observeErased m g checked input := by
  rw [observeErased, OrderedState.Partial.observe, Term.toTerm_toGraph]
  exact exec_iff m checked input PUnit.unit output

theorem observe_eq :
    Part.map boundaryResult (NestedTheta.Partial.observe (wireModel m) g input) =
      observeErased m g checked input := by
  apply Part.ext
  intro result
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨output, explicitMember, rfl⟩
    exact (returns_iff m g checked input output).mp
      ((NestedTheta.Partial.observe_eq_some (wireModel m) g input output).mp (Part.eq_some_iff.mpr explicitMember))
  · intro returned
    obtain ⟨output, rfl⟩ := (boundaryResult_bijective b).surjective result
    have explicitReturn := (returns_iff m g checked input output).mpr returned
    exact ⟨output, Part.eq_some_iff.mp
      ((NestedTheta.Partial.observe_eq_some (wireModel m) g input output).mpr explicitReturn), rfl⟩

theorem abnormal_iff (obs : Observation m) :
    abnormal m g input obs ↔
      OrderedState.Partial.abnormal (erasedModel m) checked.erase.toGraph
        (boundaryResult input).1 (boundaryResult input).2 obs := by
  rw [OrderedState.Partial.abnormal, Term.toTerm_toGraph]
  exact abnormalAt_iff m checked input PUnit.unit [] obs

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Proofs
