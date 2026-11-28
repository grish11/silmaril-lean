module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Recognition

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- Decode a typed outward region to existing acyclic code, with equality to
the original syntax at its chosen exit. -/
theorem recognize {r : Region Φ} {L : LCtx τ} {exit : Nat}
    (shape : Outward exit r) (typed : Region.HasType β.toList r L) (destination : At L exit A) :
    Nonempty {c : Code Φ β A // c.toSSA exit = r} :=
  recognize_proof shape typed destination

/-- Read back the existing exact code using the native type and shape proofs. -/
noncomputable def Endpoint.code (p : Endpoint Φ β A) : Code Φ β A :=
  (recognize p.outward p.typed rfl).some.val

theorem Endpoint.code_exact (p : Endpoint Φ β A) : p.code.toSSA 0 = p.region :=
  (recognize p.outward p.typed rfl).some.property

/-- Compile the original region using the existing single-exit translation. -/
@[expose] noncomputable def Endpoint.compile (p : Endpoint Φ β A) : Operand Φ β A :=
  p.code.toLetCase

end Silmaril.Isotope.LambdaSSA.Acyclic.Native
