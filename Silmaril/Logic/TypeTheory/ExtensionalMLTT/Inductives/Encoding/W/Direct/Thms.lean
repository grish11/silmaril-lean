module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Source
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WDirectSource

@[expose] public section

/-! Actual derivations for the original directly substituted source templates. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

theorem nextDirect_typing_iterated_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H ((S.position.lst i).lst a) p p) :
    Γ.JEqB levels H S.index (((S.next.lst i).lst a).lst p) (((S.next.lst i).lst a).lst p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextDirect_typing_iterated_of_hypotheses hH D hi ha hp

theorem nextDirect_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H S.index
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextDirect_typing_of_hypotheses hH D hi ha hp

theorem childIndexAt_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H S.index (S.childIndexAt l p) (S.childIndexAt l p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childIndexAt_typing_of_hypotheses hH D hl hp

theorem nextDirect_typing_iterated (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ ((S.position.lst i).lst a) p p) :
    Γ.JEqB levels ∅ S.index (((S.next.lst i).lst a).lst p) (((S.next.lst i).lst a).lst p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextDirect_typing_iterated D hi ha hp

theorem nextDirect_typing (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ S.index
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i))))
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextDirect_typing D hi ha hp

theorem positions_lst (S : Description) (l : Tm 0) :
    S.positions.lst l = S.positionAt (.fst l) (.snd l) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positions_lst S l

theorem childIndexAt_typing (D : IndexedFormationData S levels n Γ) {l p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ S.index (S.childIndexAt l p) (S.childIndexAt l p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childIndexAt_typing D hl hp

theorem positions_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels H (.univ n)
      (S.positions.open x) (S.positions.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positions_formation_of_hypotheses hH D

theorem root_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {t : Tm 0}
    (ht : Γ.JEqB levels H S.raw t t) :
    Γ.JEqB levels H S.index (S.root t) (S.root t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_typing_of_hypotheses hH D ht

theorem positions_formation (D : FormationData S levels n Γ) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.totalShape).JEqB levels ∅ (.univ n)
      (S.positions.open x) (S.positions.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positions_formation D

theorem rootStep_eq_headStep (S : Description) :
    S.rootStep = Tm.headStep S.totalShape S.positions S.index (.fst (.bv 0)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.rootStep_eq_headStep S

theorem root_eq_head (S : Description) (t : Tm 0) :
    S.root t = Tm.head S.totalShape S.positions S.index (.fst (.bv 0)) t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_eq_head S t

theorem root_typing (D : FormationData S levels n Γ) {t : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t t) :
    Γ.JEqB levels ∅ S.index (S.root t) (S.root t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_typing D ht

theorem successor_nextDirect_typing : Ctx.JEqB 2 ∅ .nil .nats (.succ .zero) (.succ .zero) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.successor_nextDirect_typing

theorem triple_lst_eq_bsubst (N : Tm 3) (i a p : Tm 0) :
    ((N.lst i).lst a).lst p = N.bsubst (Fin.cases p (Fin.cases a (fun _ => i))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.triple_lst_eq_bsubst N i a p

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
