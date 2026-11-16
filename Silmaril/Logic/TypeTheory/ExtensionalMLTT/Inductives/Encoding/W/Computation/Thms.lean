module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Coherence
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.HeadComputation
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WRootComputation

@[expose] public section

/-! Normalized object equality for the original root on arbitrary actual W nodes. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

theorem root_sup_beta_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {l f : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels H S.index (S.root (.sup S.totalShape S.positions l f)) (.fst l) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_sup_beta_of_hypotheses hH D hl hf

theorem root_tagged_sup_beta_of_hypotheses (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.arr (S.positions.lst (.pair i a)) S.raw) f f) :
    Γ.JEqB levels H S.index
      (S.root (.sup S.totalShape S.positions (.pair i a) f)) i :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_tagged_sup_beta_of_hypotheses hH D hi ha hf

theorem root_sup_beta (D : FormationData S levels n Γ) {l f : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst l) S.raw) f f) :
    Γ.JEqB levels ∅ S.index (S.root (.sup S.totalShape S.positions l f)) (.fst l) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_sup_beta D hl hf

theorem root_tagged_sup_beta (D : FormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.arr (S.positions.lst (.pair i a)) S.raw) f f) :
    Γ.JEqB levels ∅ S.index
      (S.root (.sup S.totalShape S.positions (.pair i a) f)) i :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_tagged_sup_beta D hi ha hf

theorem nullary_root_beta : Ctx.JEqB 2 ∅ .nil .unit
    (nullaryDescription.root nullaryRawLeaf) .star :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullary_root_beta

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
