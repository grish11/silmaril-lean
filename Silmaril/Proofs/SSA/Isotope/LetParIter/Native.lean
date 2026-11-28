module

public import Silmaril.SSA.Isotope.LetParIter.Defs

public section

namespace Silmaril.Isotope.LetParIter.Proofs

universe u v w

theorem toLetIter?_embed {ν : Type u} {Φ : Type v} {n : Nat}
    (t : LetIter.LocallyNameless.Tm ν Φ n) : toLetIter? (embed t) = some t := by
  induction t <;> simp [embed, toLetIter?, *]

variable {ν : Type u} {Φ : Type v} {n k : Nat}

theorem embed_caseIter (t : LetCase.LocallyNameless.Tm ν Φ n) :
    embed (Morphism.CaseIter.embed t) = ofLetParCase (LetParCase.embed t) := by
  induction t <;> simp [Morphism.CaseIter.embed, embed, LetParCase.embed, ofLetParCase,
    Parallel.Tm.widen, *]

private theorem up_eq (r : Fin n → Fin k) :
    LetIter.LocallyNameless.Tm.up r = Parallel.Tm.up r := rfl

theorem embed_rename (r : Fin n → Fin k) (t : LetIter.LocallyNameless.Tm ν Φ n) :
    embed (t.rename r) = (embed t).rename r := by
  induction t generalizing k <;>
    simp [LetIter.LocallyNameless.Tm.rename, Parallel.Tm.rename, embed, up_eq, *]

private theorem embed_upSub (σ : Fin n → LetIter.LocallyNameless.Tm ν Φ k) :
    (fun i => embed (LetIter.LocallyNameless.Tm.upSub σ i)) =
      Parallel.Tm.upSub (fun i => embed (σ i)) := by
  funext i
  exact Fin.cases rfl (fun j => embed_rename Fin.succ (σ j)) i

theorem embed_bsubst (σ : Fin n → LetIter.LocallyNameless.Tm ν Φ k)
    (t : LetIter.LocallyNameless.Tm ν Φ n) :
    embed (t.bsubst σ) = (embed t).bsubst (fun i => embed (σ i)) := by
  induction t generalizing k <;>
    simp [LetIter.LocallyNameless.Tm.bsubst, Parallel.Tm.bsubst, embed, embed_upSub, *]

theorem embed_pure {ε : Type w} [HasEff Φ ε] {pe : ε}
    {t : LetIter.LocallyNameless.Tm ν Φ n}
    (h : LetIter.LocallyNameless.Pure pe t) : Parallel.Pure pe (embed t) := by
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

end Silmaril.Isotope.LetParIter.Proofs
