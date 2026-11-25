module

public import Silmaril.Wasm.Institution.Operational.Blocks.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Proofs

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop)
    (sound : ∀ {a b}, Edge a b → native (emit a) (emit b))
    (readback : ∀ {a b}, native (emit a) b → ∃ out, Edge a out ∧ b = emit out)
    {types : List NumType} {result : Option NumType} {a : State} {b : C}
    (guard : Admitted types result a) :
    Relation.ReflTransGen native (emit a) b ↔
      ∃ out, Runs a out ∧ Admitted types result out ∧ b = emit out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, guard, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, ready, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback step
      exact ⟨out, path.tail edge, Blocks.closed ready edge, rfl⟩
  · rintro ⟨out, path, _, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ h => sound h) _ _ path

end Silmaril.Wasm.Institution.Operational.Blocks.Proofs
