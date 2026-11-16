module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional.Syntax.Defs
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalConstructorMap

@[expose] public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Scoped renaming agrees with changing the actual named assignment. -/
theorem term_rename {n m k : ℕ} (σ : Fin m → ETm k) (ρ : Fin n → Fin m) (t : Term n) :
    term σ (t.rename ρ) = term (σ ∘ ρ) t :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalSyntax.term_rename σ ρ t

/-- Opening a translated binder extends the assignment by its actual fresh name. -/
theorem term_lift_open {n : ℕ} (σ : Fin n → ETm 0) (t : Term (n + 1)) (x : String) :
    (term (lift σ) t).open x = term (Fin.cons (.fv x) σ) t :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalSyntax.term_lift_open σ t x

/-- Scoped one-binder substitution agrees with actual target instantiation. -/
theorem term_instantiate {n : ℕ} (σ : Fin n → ETm 0) (t : Term (n + 1)) (a : Term n) :
    term σ (t.instantiate a) = (term (lift σ) t).lst (term σ a) :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalSyntax.term_instantiate σ t a

/-- Target weakening acts pointwise on the actual source-variable assignment. -/
theorem term_wkn {n k : ℕ} (σ : Fin n → ETm k) (t : Term n) (j : ℕ) :
    (term σ t).wkn j = term (fun i => (σ i).wkn j) t :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.ExtensionalSyntax.term_wkn σ t j

end Silmaril.Logic.TypeTheory.IntensionalMLTT.Extensional
