module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Basic

/-!
# From interaction-tree bodies to trace-set functions: theorems

* `toAFun_det`: every body denotes an abstract function that is deterministic
  given the history (`AFun.Det`). The environment's answers are inputs, and
  the body's own moves are functions of them.
* `exists_not_denoted`: some abstract function is denoted by no body: a
  nondeterministic choice of result. The bodies are therefore a **restricted
  submodel** of the trace-set functions, contained in the deterministic ones.
  Nondeterministic Wasm behaviour (NaN payloads, relaxed operations) in body
  form changes the interface: the choice becomes an environment event. The
  trace-set functions model it directly as a set of behaviours, so the two
  readings put may/must quantifiers in different places.

Not claimed: injectivity of `toAFun` (trap payloads and infinite productive
runs are forgotten); that `toAFun` maps Kleisli composition to `AFun.seq`; and
a characterisation of the image (deterministic functions that are receptive to
every answer and total).
-/

public section

namespace Silmaril.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body

universe u

/-- Denoted functions are deterministic given the history. -/
theorem toAFun_det {E : Sig.{u}} {S T A B : Type (u + 1)} (f : Hom E S T A B) :
    AFun.Det (toAFun f) :=
  Silmaril.Proofs.Wasm.Abstract.BodyTrace.toAFun_det f

/-- Not every trace-set function is denoted by a body. -/
theorem exists_not_denoted :
    ∃ g : AFun (liftSig Sig.empty.{0}) PUnit.{2} PUnit.{2} (ULift.{1} Bool),
      ∀ (T : Type 1) (f : Hom Sig.empty.{0} PUnit.{2} T PUnit.{2} (ULift.{1} Bool)), toAFun f ≠ g :=
  ⟨Silmaril.Proofs.Wasm.Abstract.BodyTrace.coin,
    fun _ f => Silmaril.Proofs.Wasm.Abstract.BodyTrace.coin_not_denoted f⟩

end Silmaril.Wasm.Abstract.BodyTrace
