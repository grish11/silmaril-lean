module

public import Silmaril.SSA.Isotope.Institution.Parallel.Relabel.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Parallel.Relabel

@[expose] public section

namespace Silmaril.Isotope.Parallel

open Silmaril.Isotope.Institution CategoryTheory

universe u v w

variable {tier target : Tier} {ν : Type v} {Φ Ψ : Type w} {n : Nat}

@[simp] theorem Tm.mapInstr_id (a : Tm tier ν Φ n) : a.mapInstr id = a :=
  InstitutionProofs.Tm.map_id a

theorem Tm.mapInstr_comp {Ω : Type w} (f : Φ → Ψ) (g : Ψ → Ω) (a : Tm tier ν Φ n) :
    (a.mapInstr f).mapInstr g = a.mapInstr (g ∘ f) :=
  InstitutionProofs.Tm.map_comp f g a

@[simp] theorem Tm.mapInstr_widen (h : Tier.Inclusion tier target) (f : Φ → Ψ) (a : Tm tier ν Φ n) :
    (a.widen h).mapInstr f = (a.mapInstr f).widen h :=
  InstitutionProofs.Tm.map_widen f h a

variable {τ ε : Type u} {S S' S'' : InstrSig τ ε} {e : ε} {a b : Tm tier ν S.Instr n}

theorem Pure.mapInstr (f : S ⟶ S') (h : Pure e a) : Pure e (a.mapInstr f.instr) :=
  InstitutionProofs.pure_map f h

theorem SeqRule.mapInstr (f : S ⟶ S') (h : SeqRule e a b) :
    SeqRule e (a.mapInstr f.instr) (b.mapInstr f.instr) :=
  InstitutionProofs.seqRule_map f h

theorem ParRule.mapInstr (f : S ⟶ S') (h : ParRule e a b) :
    ParRule e (a.mapInstr f.instr) (b.mapInstr f.instr) :=
  InstitutionProofs.parRule_map f h

theorem CaseRule.mapInstr (f : S ⟶ S') (h : CaseRule e a b) :
    CaseRule e (a.mapInstr f.instr) (b.mapInstr f.instr) :=
  InstitutionProofs.caseRule_map f h

variable [HasProduct τ] [HasUnit τ] [CaseTypes tier τ] [DecidableEq ν]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ}

theorem HasType.mapInstr (f : S ⟶ S') (h : HasType S.Instr Γ β a A) :
    HasType S'.Instr Γ β (a.mapInstr f.instr) A :=
  InstitutionProofs.hasType_map f h

theorem Derivation.mapInstr_id (d : Derivation S.Instr Γ β a A) :
    HEq (d.mapInstr (𝟙 S)) d :=
  InstitutionProofs.derivation_map_id d

theorem Derivation.mapInstr_comp (f : S ⟶ S') (g : S' ⟶ S'')
    (d : Derivation S.Instr Γ β a A) :
    HEq ((d.mapInstr f).mapInstr g) (d.mapInstr (f ≫ g)) :=
  InstitutionProofs.derivation_map_comp f g d

/-- Relabel the typed congruence, assuming preservation of the extra schemes. -/
theorem Equiv.mapInstr (f : S ⟶ S') {rules : EqScheme tier ν S.Instr}
    {rules' : EqScheme tier ν S'.Instr}
    (extra : ∀ {k} {l r : Tm tier ν S.Instr k}, rules l r →
      rules' (l.mapInstr f.instr) (r.mapInstr f.instr))
    (h : Equiv e rules Γ β a b A) :
    Equiv e rules' Γ β (a.mapInstr f.instr) (b.mapInstr f.instr) A :=
  InstitutionProofs.equiv_map f extra h

end Silmaril.Isotope.Parallel

namespace Silmaril.Isotope

open Institution CategoryTheory

universe u v

variable {τ ε : Type u} {S S' : InstrSig τ ε} {e : ε}
  {ν : Type v} [DecidableEq ν] {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

theorem LetPar.mapInstr_equiv [HasProduct τ] [HasUnit τ] (f : S ⟶ S')
    {a b : LetPar.Tm ν S.Instr n} (h : LetPar.Equiv e Γ β a b A) :
    LetPar.Equiv e Γ β (a.mapInstr f.instr) (b.mapInstr f.instr) A :=
  Parallel.Equiv.mapInstr f (fun h => h) h

theorem LetParCase.mapInstr_equiv [TypeFormers τ] (f : S ⟶ S')
    {a b : LetParCase.Tm ν S.Instr n} (h : LetParCase.Equiv e Γ β a b A) :
    LetParCase.Equiv e Γ β (a.mapInstr f.instr) (b.mapInstr f.instr) A :=
  Parallel.Equiv.mapInstr f (Parallel.CaseRule.mapInstr f) h

end Silmaril.Isotope
