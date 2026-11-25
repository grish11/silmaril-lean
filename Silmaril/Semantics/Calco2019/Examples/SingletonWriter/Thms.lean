module

public import Silmaril.Semantics.Calco2019.Examples.SingletonWriter.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.SingletonWriter

/-! # The singleton writer extension and its bind -/

public section

universe u

namespace Silmaril.Calco2019.Examples.SingletonWriter

variable {A X Y : Type u}

@[simp] theorem observe_result (word : List A) (x : X) :
    observe (result word x) = .inl (word, x) :=
  Proofs.observe_result word x

@[simp] theorem observe_divergence : observe (divergence : Model A X) = .inr PUnit.unit :=
  Proofs.observe_divergence

@[simp] theorem observe_pure (x : X) : observe (pure x : Model A X) = .inl ([], x) := by
  rw [Proofs.pure_eq, observe_result]

/-- Sequencing concatenates words from two successful runs. Any divergence has the
one divergence observation. -/
theorem observe_bind (p : Model A X) (k : X → Model A Y) :
    observe (p >>= k) =
      match observe p with
      | .inr _ => .inr PUnit.unit
      | .inl (word, x) =>
        match observe (k x) with
        | .inr _ => .inr PUnit.unit
        | .inl (suffix, y) => .inl (word ++ suffix, y) :=
  Proofs.observe_bind p k

/-- Example 20(4), with the left action on a singleton. The resulting monad supports
iteration for every loop body. -/
theorem elgot_isElgot (A : Type u) : (elgot A).IsElgot :=
  Proofs.elgot_isElgot A

end Silmaril.Calco2019.Examples.SingletonWriter
