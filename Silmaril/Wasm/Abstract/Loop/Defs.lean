module

public import Silmaril.Wasm.Abstract.Body.Defs

/-!
# Abstract Wasm loops

**Scope.** These are loops of *abstract* bodies (`BodyM`), and the theorems
about them are statements about abstract body denotations. They are not
theorems about executing Core Wasm `loop` instructions: no bridge from Core
reduction to these bodies is proved here. The Wasm instructions named below
only say which abstract body is meant.

A Wasm `loop` whose body either falls out with a result or branches back to
the loop label is Elgot iteration of abstract bodies: the body returns
`inl b` to leave the loop with `b`, and `inr a` to branch back (`br` to the
loop label) with the new loop argument `a`. Locals and operands travel in
`A`; the module state is threaded by `BodyM`.

Three loops show the three ways a loop can fail to return:

* `spin`: `loop br 0 end`, branching back forever without an import call:
  silent divergence, although no single iteration diverges;
* `trapLoop t`: `loop unreachable end`, a trap in the first iteration;
* `pollLoop m`: `loop call m; br 0 end`, calling the import `m` forever: an
  infinite *productive* run.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.Loop

open Silmaril.Games Silmaril.Wasm.Abstract.Body

universe u

variable {E : Sig.{u}} {S T A B : Type (u + 1)}

/-- A loop: the body exits with `inl b` and branches back with `inr a`. -/
noncomputable def loop (F : Hom E S T A (B ⊕ A)) : Hom E S T A B := Silmaril.Elgot.iter F

/-- Branch back forever, silently. -/
noncomputable def spin : Hom E S T A B := loop fun a => pure (.inr a)

/-- Trap in the first iteration. -/
noncomputable def trapLoop (t : T) : Hom E S T A B := loop fun _ => trap t

/-- Call the import `m` and branch back, forever. -/
noncomputable def pollLoop (m : E.Op) : Hom E S T A B :=
  loop fun a => callImport m >>= fun _ => pure (.inr a)

/-- Two imports, `true` and `false`, each answered with no data: the smallest
signature with two distinct forever-import streams. -/
def twoImports : Sig.{0} := ⟨Bool, fun _ => PUnit⟩

end Silmaril.Wasm.Abstract.Loop
