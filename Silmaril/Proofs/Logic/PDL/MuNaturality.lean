module

public import Silmaril.Proofs.Logic.PDL.MuTranslation

@[expose] public section
namespace Silmaril.Logic.PDL
open CategoryTheory Silmaril.Logic.Institution

mutual
  theorem Formula.toMu_map {S T : Signature} (f : S ⟶ T) (p : Formula S) :
      (p.map f).toMu = p.toMu.map f := by
    cases p with
    | atom a => rfl
    | bot => rfl
    | neg p =>
        change (p.map f).toMu.dual = p.toMu.dual.map f
        rw [Formula.toMu_map f p, ModalMu.Formula.dual_map]
    | conj p q => exact congrArg₂ ModalMu.Formula.conj (Formula.toMu_map f p) (Formula.toMu_map f q)
    | disj p q => exact congrArg₂ ModalMu.Formula.disj (Formula.toMu_map f p) (Formula.toMu_map f q)
    | box a p =>
        change ((a.map f).toMu (p.map f).toMu.dual).dual = (a.toMu p.toMu.dual).dual.map f
        rw [Formula.toMu_map f p, ModalMu.Formula.dual_map, Program.toMu_map f a,
          ModalMu.Formula.dual_map]
    | diamond a p =>
        change (a.map f).toMu (p.map f).toMu = (a.toMu p.toMu).map f
        rw [Formula.toMu_map f p, Program.toMu_map f a]
  termination_by sizeOf p

  theorem Program.toMu_map {S T : Signature} (f : S ⟶ T) (a : Program S)
      {n : Nat} (c : ModalMu.Formula S n) :
      (a.map f).toMu (c.map f) = (a.toMu c).map f := by
    cases a with
    | action a => rfl
    | seq a b =>
        change (a.map f).toMu ((b.map f).toMu (c.map f)) = (a.toMu (b.toMu c)).map f
        rw [Program.toMu_map f b, Program.toMu_map f a]
    | choice a b => exact congrArg₂ ModalMu.Formula.disj (Program.toMu_map f a c) (Program.toMu_map f b c)
    | star a =>
        change ModalMu.Formula.mu (.disj (c.map f).shift ((a.map f).toMu (.var 0))) =
          .mu (.disj (c.shift.map f) ((a.toMu (.var 0)).map f))
        have hs : (c.map f).shift = c.shift.map f := c.renameVars_map f Fin.succ
        rw [hs]
        exact congrArg (fun q => ModalMu.Formula.mu (.disj (c.shift.map f) q))
          (Program.toMu_map f a (.var (0 : Fin (n + 1))))
    | test p =>
        change ModalMu.Formula.conj ((p.map f).toMu.closedAt n) (c.map f) =
          .conj ((p.toMu.closedAt n).map f) (c.map f)
        rw [Formula.toMu_map f p]
        exact congrArg (fun q => ModalMu.Formula.conj q (c.map f))
          (p.toMu.renameVars_map f Fin.elim0)
  termination_by sizeOf a
end

/-- Identity signatures and models, with the verified continuation translation. -/
def muNatural : institution ⟶ ModalMu.institution where
  app S := ⟨Formula.toMu, 𝟭 _, fun M p => Formula.toMu_correct M p M.point⟩
  naturality := by
    intro S T f
    exact Room.hom_ext (funext (Formula.toMu_map f)) rfl

def pdlToMu : Inst.CoHom ⟨Signature, institution⟩ ⟨Signature, ModalMu.institution⟩ :=
  ⟨𝟭 _, muNatural⟩

theorem pdlToMu_modelExpansive : pdlToMu.ModelExpansive := fun _ M => ⟨M, rfl⟩

end Silmaril.Logic.PDL
