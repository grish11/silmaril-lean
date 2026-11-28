module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.InstructionMap

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.InstructionMap.Proofs

universe u v a s

variable {Φ : Type u} {Ψ : Type v} {α : Type a} {σ : Type s}
variable {instr : Φ → Value α → σ → Value α → σ → Prop}
variable {instr' : Ψ → Value α → σ → Value α → σ → Prop}
variable (f : Φ → Ψ)
variable (step : ∀ i input before output after,
  instr' (f i) input before output after → instr i input before output after)

include step

private theorem term_reflect {env : Env α} {target : LambdaSSA.Tm Ψ}
    {start finish : σ} {value : Value α} (ran : Tm.Eval instr' env target start value finish) :
    ∀ source : LambdaSSA.Tm Φ, target = source.mapInstr f →
      Tm.Eval instr env source start value finish := by
  induction ran with
  | var => intro source same; cases source <;> cases same; exact .var
  | op _ called ih =>
    intro source same
    cases source <;> cases same
    exact .op (ih _ rfl) (step _ _ _ _ _ called)
  | let₁ _ _ left right =>
    intro source same; cases source <;> cases same; exact .let₁ (left _ rfl) (right _ rfl)
  | unit => intro source same; cases source <;> cases same; exact .unit
  | pair _ _ left right =>
    intro source same; cases source <;> cases same; exact .pair (left _ rfl) (right _ rfl)
  | let₂ _ _ left right =>
    intro source same; cases source <;> cases same; exact .let₂ (left _ rfl) (right _ rfl)
  | inl _ ih => intro source same; cases source <;> cases same; exact .inl (ih _ rfl)
  | inr _ ih => intro source same; cases source <;> cases same; exact .inr (ih _ rfl)
  | case_inl _ _ test left =>
    intro source same; cases source <;> cases same; exact .case_inl (test _ rfl) (left _ rfl)
  | case_inr _ _ test right =>
    intro source same; cases source <;> cases same; exact .case_inr (test _ rfl) (right _ rfl)

theorem region_reflect {env : Env α} {target : LambdaSSA.Region Ψ}
    {start finish : σ} {label : Nat} {value : Value α}
    (ran : Region.Eval instr' env target start label value finish) :
    ∀ source : LambdaSSA.Region Φ, target = source.mapInstr f →
      Region.Eval instr env source start label value finish := by
  induction ran using Region.Eval.rec
      (motive_2 := fun env n blocks entry arg start label value finish _ =>
        ∀ source : Fin n → LambdaSSA.Region Φ, (∀ i, blocks i = (source i).mapInstr f) →
          Region.Follow instr env source entry arg start label value finish) with
  | br arg =>
    intro source same; cases source <;> cases same
    exact .br (term_reflect f step arg _ rfl)
  | let₁ arg _ ih =>
    intro source same; cases source <;> cases same
    exact .let₁ (term_reflect f step arg _ rfl) (ih _ rfl)
  | let₂ arg _ ih =>
    intro source same; cases source <;> cases same
    exact .let₂ (term_reflect f step arg _ rfl) (ih _ rfl)
  | case_inl arg _ ih =>
    intro source same; cases source <;> cases same
    exact .case_inl (term_reflect f step arg _ rfl) (ih _ rfl)
  | case_inr arg _ ih =>
    intro source same; cases source <;> cases same
    exact .case_inr (term_reflect f step arg _ rfl) (ih _ rfl)
  | cfg _ _ entry follow =>
    intro source same; cases source <;> cases same
    exact .cfg (entry _ rfl) (follow _ (fun _ => rfl))
  | exit outside _ _ => exact .exit outside
  | step inside _ _ head tail source same =>
    exact .step inside (head _ (same _)) (tail source same)

end Silmaril.Isotope.LambdaSSA.Semantics.InstructionMap.Proofs
