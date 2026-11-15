module

public import Silmaril.Wasm.Abstract.Body.Defs

/-!
# Abstract Wasm function bodies: collapse preserves iteration

Collapsing is postcomposition with the continuation that sends a trap to
`diverge`. By naturality of tree iteration it moves inside the loop, where
a trapping iteration diverges, so the collapsed loop diverges as well.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Body

open Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Elgot.ITree

universe u

variable {E : Sig.{u}} {S T : Type (u + 1)}

/-- The continuation of `collapse`: a trap diverges. -/
noncomputable def collapseK {X : Type (u + 1)} : Except T X → Tree (SigEv E) X
  | .ok p => pure p
  | .error _ => diverge

theorem collapse_apply {A : Type (u + 1)} (x : BodyM E S T A) (s : S) :
    collapse x s = (x.run s).run >>= collapseK := by
  unfold collapse
  congr 1
  funext r
  cases r <;> rfl

theorem collapse_iter {A B : Type (u + 1)} (F : A → BodyM E S T (B ⊕ A)) (a : A) :
    collapse (Silmaril.Elgot.iter F a) = Silmaril.Elgot.iter (fun a => collapse (F a)) a := by
  funext s
  have hn := congrFun (Silmaril.Elgot.LawfulElgotMonad.naturality
    (Silmaril.Elgot.ExceptT.body (Silmaril.Elgot.StateT.body F))
    (collapseK (E := E) (T := T) (X := B × S))) (a, s)
  rw [collapse_apply]
  change Silmaril.Elgot.iter (Silmaril.Elgot.ExceptT.body (Silmaril.Elgot.StateT.body F)) (a, s) >>=
    _ = Silmaril.Elgot.iter (Silmaril.Elgot.StateT.body (fun a => collapse (F a))) (a, s)
  refine hn.trans (congrFun (congrArg Silmaril.Elgot.iter (funext fun p => ?_)) (a, s))
  simp only [Silmaril.Elgot.mapReturn, Silmaril.Elgot.ExceptT.body, Silmaril.Elgot.StateT.body,
    ExceptT.run_bind, bind_assoc, Function.comp]
  rw [show StateT.run (collapse (F p.1)) p.2 = collapse (F p.1) p.2 from rfl, collapse_apply,
    bind_assoc]
  congr 1
  funext r
  rcases r with e | ⟨b | a', s'⟩ <;>
    simp [collapseK, Silmaril.Elgot.ExceptT.distribute, Silmaril.Elgot.StateT.distribute]

end Silmaril.Proofs.Wasm.Abstract.Body
