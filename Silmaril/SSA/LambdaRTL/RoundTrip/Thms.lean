module

public import Silmaril.SSA.LambdaRTL.RoundTrip.Defs
public import Silmaril.SSA.LambdaRTL.Nameless.Thms
public import Silmaril.SSA.LambdaRTL.Version.Thms
import Silmaril.Proofs.SSA.LambdaRTL.RoundTrip.Deversion

/-! Versioning and deversioning preserve the exit and payload of acyclic λRTL
in the same initial store. The observation is a computation of a label and
payload in the model's monad. -/

@[expose] public section

namespace Silmaril.SSA.LambdaRTL

open RoundTrip (deversion)

universe v w

variable {V L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
variable [DecidableEq V] [Infinite V]

@[simp] theorem deversion_zero (support : Finset (V × ℕ)) (name : V) :
    deversion support (name, 0) = name := by simp [deversion]

theorem deversion_injOn (support : Finset (V × ℕ)) : Set.InjOn (deversion support) support :=
  Silmaril.Proofs.SSA.LambdaRTL.RoundTrip.deversion_injOn support

/-- The pair law makes the tuple transfers introduced by versioning transparent.
Infinitude supplies fresh names for the finitely many nonzero versions. -/
theorem roundTrip_evalObs [Monad M] [LawfulMonad M] [DecidableEq L]
    (m : Model F M α) (pairs : m.PairLawful) (r : Region V L F) (store : V → α) :
    ((Version.versionTop r).rename (deversion (Version.versionTop r).vars)).evalObs m store =
      r.evalObs m store := by
  rw [Region.evalObs_rename_on m (deversion_injOn _) _ (fun _ h => h)
    (σ := store ∘ deversion (Version.versionTop r).vars) (fun _ _ => rfl)]
  exact Version.versionTop_evalObs m pairs r store _ (fun x => by simp)

end Silmaril.SSA.LambdaRTL
