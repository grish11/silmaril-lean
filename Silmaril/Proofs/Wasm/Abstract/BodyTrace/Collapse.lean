module

public import Silmaril.Wasm.Abstract.BodyTrace.Defs
public import Silmaril.Games.Abstract.FunctionIter.Defs
public import Silmaril.Semantics.ITree.Thms
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Bind
import Silmaril.Proofs.Wasm.Abstract.BodyTrace.Iter

/-!
# The trap ≈ divergence observation of a denoted body

The collapsed observations of `toAFun f` are exactly the finite paths of the
collapsed body `collapse (f a)`: a trap path of the body becomes a diverging
path of the collapsed tree, which the observation also reads as an abort.
So bodies with equal collapse have trap ≈ divergence equivalent denotations.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.BodyTrace

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Body
  Silmaril.Wasm.Abstract.BodyTrace Silmaril.Elgot.ITree

universe u

variable {E : Sig.{u}} {S T A B : Type (u + 1)}

/-- The continuation of `collapse`. -/
noncomputable def trapDiverge {X : Type (u + 1)} : Except T X → Tree (SigEv E) X
  | .ok p => pure p
  | .error _ => diverge

theorem collapse_eq_bind (x : BodyM E S T B) (s : S) :
    collapse x s = (x.run s).run >>= trapDiverge := by
  unfold collapse
  congr 1
  funext r
  cases r <;> rfl

/-- The end of a collapsed path, as a collapsed end. -/
def cendOf : PathEnd (B × S) → CEnd S B
  | .val (b, s) => .ret b s
  | .div => .abort

theorem obsCollapse_toAFun (f : Hom E S T A B) (s : S) (a : A) :
    AFun.obsCollapse '' toAFun f s a =
      {x | ∃ cs r, Path (collapse (f a) s) cs r ∧ x = (cs.map liftCall, cendOf r)} := by
  ext x
  constructor
  · rintro ⟨_, ⟨cs, r, hp, rfl⟩, rfl⟩
    rw [collapse_eq_bind]
    rcases r with (e | ⟨b, s'⟩) | _
    · exact ⟨cs ++ [], .div, path_bind_ret hp (Path.div rfl), by
        simp [AFun.obsCollapse, endOf, cendOf, End.collapse]⟩
    · exact ⟨cs ++ [], .val (b, s'), path_bind_ret hp (Path.ret rfl), by
        simp [AFun.obsCollapse, endOf, cendOf, End.collapse]⟩
    · exact ⟨cs, .div, path_bind_div hp, by simp [AFun.obsCollapse, endOf, cendOf, End.collapse]⟩
  · rintro ⟨cs, r, hp, rfl⟩
    rw [collapse_eq_bind] at hp
    rcases path_bind_inv hp with ⟨cs₁, cs₂, v, rfl, h₁, h₂⟩ | ⟨rfl, h₁⟩
    · rcases v with e | ⟨b, s'⟩
      · obtain ⟨rfl, rfl⟩ := path_diverge_inv h₂
        exact ⟨_, ⟨cs₁, _, h₁, rfl⟩, by simp [AFun.obsCollapse, endOf, cendOf, End.collapse]⟩
      · obtain ⟨rfl, rfl⟩ := path_ret_inv rfl h₂
        exact ⟨_, ⟨cs₁, _, h₁, rfl⟩, by simp [AFun.obsCollapse, endOf, cendOf, End.collapse]⟩
    · exact ⟨_, ⟨cs, _, h₁, rfl⟩, by simp [AFun.obsCollapse, endOf, cendOf, End.collapse]⟩

theorem obsCollapse_of_collapse {f g : Hom E S T A B} (h : ∀ a, collapse (f a) = collapse (g a)) :
    AFun.ObsEquiv AFun.obsCollapse (toAFun f) (toAFun g) := fun s a => by
  rw [obsCollapse_toAFun, obsCollapse_toAFun, h a]

end Silmaril.Proofs.Wasm.Abstract.BodyTrace
