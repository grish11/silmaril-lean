module

public import Silmaril.Proofs.Wasm.Abstract.ExposePTyped.Fwd

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePTyped.Thms`: the converse of the forward tensor. A
checked run of `EvalOXP C` on a stack with a passive suffix, under an arity-respecting oracle,
is a run on the stack without it, to the same store and frame, its result whiskered and read at
its target's arity (`Bwd`). The checked heights of the run without the suffix come from the
forward invariants (`evalOXP_fwd`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePTyped

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.CallXT (typeArity tailAnn)

variable {H : Type}

/-! ## Stacks with a suffix -/

theorem normal_of_trim {L : List Nat} {r : Nat} {o : POut} {rest w : List Val}
    (h : trimO L r (.flow (.normal w)) = trimO L r (whiskO rest o)) :
    ∃ v, o = .flow (.normal v) ∧ w = v ++ rest := by
  rcases o with (v | ⟨l, v⟩ | v | _ | a) | ⟨a, args, n⟩ <;>
    simp [trimO, whiskO] at h
  exact ⟨v, rfl, h⟩

theorem abrupt_of_trim {L : List Nat} {r : Nat} {o o' : POut} {rest : List Val}
    (ho' : ¬ o'.IsNormal) (h : trimO L r o' = trimO L r (whiskO rest o)) : ¬ o.IsNormal := by
  intro hn
  rcases o with (v | ⟨l, v⟩ | v | _ | a) | ⟨a, args, n⟩ <;>
    simp only [POut.IsNormal, Flow.IsNormal] at hn
  have := trimO_abrupt (L := L) (r := r) ho'
  rw [h] at this
  exact this trivial

theorem cons_of_append {a : Val} {x v rest : List Val} (h : a :: x = v ++ rest)
    (hv : 1 ≤ v.length) : ∃ y, v = a :: y ∧ x = y ++ rest := by
  rcases v with _ | ⟨b, y⟩
  · simp at hv
  · simp only [List.cons_append, List.cons.injEq] at h
    exact ⟨y, by rw [h.1], h.2⟩

theorem wFl_eq_normal {rest w : List Val} {fl : Flow} (h : wFl rest fl = .normal w) :
    ∃ v, fl = .normal v ∧ w = v ++ rest := by
  rcases fl with v | ⟨l, v⟩ | v | _ | a <;> simp [wFl] at h
  exact ⟨v, rfl, h.symm⟩

theorem evalFlat_unwhisk {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {s s' : Store H} {f f' : Frame} {stk rest : List Val}
    {i : Instr} {o : Option Nat} {fl' : Flow}
    (hc : flatChkE ext F mi nl ret labels stk.length i = some o)
    (h : evalFlat s f (stk ++ rest) i = some (s', f', fl')) :
    ∃ fl, evalFlat s f stk i = some (s', f', fl) ∧ fl' = wFl rest fl := by
  rw [evalFlat_whisk (stackPure_of_evalFlat h) hc rest] at h
  obtain ⟨⟨s₀, f₀, fl⟩, h₀, he⟩ := Option.map_eq_some_iff.1 h
  simp only [wE, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨fl, h₀, rfl⟩

theorem tailRes_unappend {s : Store H} {f : Frame} {i : Instr} {stk rest : List Val}
    {p : Option (Nat × List Val)} (h : TailRes s f i (stk ++ rest) p)
    (hn : tailPop i ≤ stk.length) :
    (∀ fa w, p = some (fa, w) → TailRes s f i stk (some (fa, stk.drop (tailPop i)))) ∧
      (p = none → TailRes s f i stk none) := by
  generalize hb : stk ++ rest = big at h
  cases h with
  | direct hfi =>
    refine ⟨fun fa w hp => ?_, fun hp => by cases hp⟩
    cases hp
    exact .direct hfi
  | @indirect x y ad i' fa stk' hres =>
    obtain ⟨y', rfl, -⟩ := cons_of_append hb.symm (by simpa [tailPop] using hn)
    refine ⟨fun fa' w hp => ?_, fun hp => by cases hp⟩
    cases hp
    exact .indirect hres
  | @indirectTrap x y ad i' stk' hres =>
    obtain ⟨y', rfl, -⟩ := cons_of_append hb.symm (by simpa [tailPop] using hn)
    exact ⟨fun _ _ hp => (by cases hp), fun _ => .indirectTrap hres⟩
  | @ref y fa stk' =>
    obtain ⟨y', rfl, -⟩ := cons_of_append hb.symm (by simpa [tailPop] using hn)
    refine ⟨fun fa' w hp => ?_, fun hp => by cases hp⟩
    cases hp
    exact .ref
  | @refNull y stk' =>
    obtain ⟨y', rfl, -⟩ := cons_of_append hb.symm (by simpa [tailPop] using hn)
    exact ⟨fun _ _ hp => (by cases hp), fun _ => .refNull⟩

theorem tailPop_le {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {p : Option (Nat × List Val)} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} {k : Nat} {o : Option Nat} (h : TailRes s f i stk p)
    (hc : flatChkE tExt F mi nl ret labels k i = some o) : tailPop i ≤ k := by
  cases h with
  | direct => simp [tailPop]
  | @indirect x y =>
    simp only [flatChkE, tExt, extStep] at hc
    cases hta : typeArity mi y <;> simp only [hta, Option.map_none, Option.map_some] at hc
    · cases hc
    · split at hc
      · simp only [tailPop]; omega
      · cases hc
  | @indirectTrap x y =>
    simp only [flatChkE, tExt, extStep] at hc
    cases hta : typeArity mi y <;> simp only [hta, Option.map_none, Option.map_some] at hc
    · cases hc
    · split at hc
      · simp only [tailPop]; omega
      · cases hc
  | @ref y =>
    simp only [flatChkE, tExt, extStep] at hc
    cases hta : typeArity mi y <;> simp only [hta, Option.map_none, Option.map_some] at hc
    · cases hc
    · split at hc
      · simp only [tailPop]; omega
      · cases hc
  | @refNull y =>
    simp only [flatChkE, tExt, extStep] at hc
    cases hta : typeArity mi y <;> simp only [hta, Option.map_none, Option.map_some] at hc
    · cases hc
    · split at hc
      · simp only [tailPop]; omega
      · cases hc

theorem one_le_callIndirect {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {k : Nat} {o : Option Nat} {x : TableIdx} {y : TypeIdx}
    (hc : flatChkE (ehExt tags) F mi nl ret labels k (.callIndirect x y) = some o) : 1 ≤ k := by
  simp only [flatChkE, ehExt, tExt, extStep] at hc
  cases hta : typeArity mi y <;> simp only [hta, Option.map_none, Option.map_some] at hc
  · cases hc
  · split at hc
    · omega
    · cases hc

theorem one_le_callRef {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {k : Nat} {o : Option Nat} {y : TypeIdx}
    (hc : flatChkE (ehExt tags) F mi nl ret labels k (.callRef y) = some o) : 1 ≤ k := by
  simp only [flatChkE, ehExt, tExt, extStep] at hc
  cases hta : typeArity mi y <;> simp only [hta, Option.map_none, Option.map_some] at hc
  · cases hc
  · split at hc
    · omega
    · cases hc

theorem one_le_throwRef {tags : List TagInst} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {labels : List Nat} {k : Nat} {o : Option Nat}
    (hc : flatChkE (ehExt tags) F mi nl ret labels k .throwRef = some o) : 1 ≤ k := by
  simp only [flatChkE, ehExt, extStep] at hc
  split at hc
  · assumption
  · cases hc

theorem throw_le {tags : List TagInst} {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat}
    {ti : TagInst} {ts : Validation.Ty (.list .val)} {nl ret : Nat} {labels : List Nat} {k : Nat}
    {o : Option Nat} (hT : s.tags = tags) (ht : s.tag? f x = some (ta, ti))
    (he : Validation.Expand ti.type (.func ts .nil))
    (hc : flatChkE (ehExt tags) s.funcs f.module nl ret labels k (.throw x) = some o) :
    ts.length ≤ k := by
  simp only [flatChkE, ehExt, extStep] at hc
  cases hp : tagFields tags f.module x with
  | none => simp [hp] at hc
  | some p =>
    simp only [hp, Option.map_some] at hc
    split at hc
    · obtain ⟨ta', ti', ts', ht', he', hl⟩ := tag_of_tagFields hT hp
      rw [ht] at ht'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ht')
      have := (Validation.Expand.iff.mp he).symm.trans (Validation.Expand.iff.mp he')
      simp only [Option.some.injEq] at this
      cases this
      omega
    · cases hc

/-! ## The converse -/

/-- The backward statement for one run, on a stack with a suffix. -/
def Bwd (Γ : Ctx H) (C : Abstract.CallRel H) (s : Store H) (f : Frame) (big : List Val)
    (es : List BExpr) (r : Store H × Frame × POut) : Prop :=
  ∀ {stk rest : List Val} {labels : List Nat} {ret : Nat} {oc : Option Nat}, big = stk ++ rest →
    Γ.Good s →
    chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some stk.length) es = some oc →
    ∃ o, EvalOXP C s f stk es (r.1, r.2.1, o) ∧
      trimO labels ret r.2.2 = trimO labels ret (whiskO rest o)

variable {Γ : Ctx H} {C : Abstract.CallRel H}

theorem bwd_cont {s s₁ : Store H} {f f₁ : Frame} {big X rest : List Val} {es : List BExpr}
    {r : Store H × Frame × POut} {labels : List Nat} {ret : Nat} {oc : Option Nat} {n : Nat}
    (hg : Γ.Good s) (hg₁ : Γ.Good s₁) (hm : f₁.module = f.module)
    (hl : f₁.locals.length = f.locals.length)
    (hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length ret labels (some n) es = some oc)
    (hn : X.length = n) (hb : big = X ++ rest) (ih : Bwd Γ C s₁ f₁ big es r) :
    ∃ o, EvalOXP C s₁ f₁ X es (r.1, r.2.1, o) ∧
      trimO labels ret r.2.2 = trimO labels ret (whiskO rest o) := by
  apply ih hb hg₁
  rw [chk_eq (good_funcs hg hg₁) hm hl, hn]; exact hc

/-- **The backward tensor.** -/
theorem evalOXP_bwd (hC : ArityResp Γ C) {s : Store H} {f : Frame} {big : List Val}
    {es : List BExpr} {r : Store H × Frame × POut} (d : EvalOXP C s f big es r) :
    Bwd Γ C s f big es r := by
  induction d with
  | nil =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    exact ⟨_, .nil, rfl⟩
  | argsAbort _ ho iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, -⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    exact ⟨o, .argsAbort d' (abrupt_of_trim ho e'), e'⟩
  | @callOk s s₁ s₂ f f₁ big stk₁' vs x args es a fi ps rs fl r hargs hfi hty hcall hvs hk iha
      ihk =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨stk₁, rfl, rfl⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some stk₁.length := go₁
    obtain ⟨p, q, hpq, hp, ho₁⟩ := flatChk_call (flatChkE_call (hbk _ hoa))
    have hpq' := callArity_eq hfi hty
    rw [good_funcs hg g₁, m₁, hpq, Option.some.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨rfl, rfl⟩ := hpq'
    rw [List.take_append_of_le_length hp] at hcall
    obtain ⟨g₂, hlen⟩ := hC _ _ _ _ _ hcall g₁
    have hrs := hlen fi ps rs vs (funcs_of_func? hfi) hty hvs
    obtain ⟨o', dk, ek⟩ := bwd_cont hg g₂ m₁ l₁ (ho₁ ▸ h2) (len_take_drop hrs hp)
      (take_drop_append hp) ihk
    exact ⟨o', .callOk d' hfi hty hcall hvs dk, ek⟩
  | @callTrap s s₁ s₂ f f₁ big stk₁' x args es a fi ps rs hargs hfi hty hcall iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨stk₁, rfl, rfl⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, -, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some stk₁.length := go₁
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call (hbk _ hoa))
    have hpq' := callArity_eq hfi hty
    rw [good_funcs hg g₁, m₁, hpq, Option.some.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨rfl, rfl⟩ := hpq'
    rw [List.take_append_of_le_length hp] at hcall
    exact ⟨_, .callTrap d' hfi hty hcall, rfl⟩
  | @callThrow s s₁ s₂ f f₁ big stk₁' x args es a fi ps rs t hargs hfi hty hcall iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨stk₁, rfl, rfl⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, -, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some stk₁.length := go₁
    obtain ⟨p, q, hpq, hp, -⟩ := flatChk_call (flatChkE_call (hbk _ hoa))
    have hpq' := callArity_eq hfi hty
    rw [good_funcs hg g₁, m₁, hpq, Option.some.injEq, Prod.mk.injEq] at hpq'
    obtain ⟨rfl, rfl⟩ := hpq'
    rw [List.take_append_of_le_length hp] at hcall
    exact ⟨_, .callThrow d' hfi hty hcall, rfl⟩
  | @opOk s s₁ s₂ f f₁ f₂ big stk₁' stk₂' i args es r hi hargs hflat hk iha ihk =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨stk₁, rfl, rfl⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hbk _ hoa
    obtain ⟨fl, hfl, hw⟩ := evalFlat_unwhisk hck hflat
    obtain ⟨stk₂, rfl, rfl⟩ := wFl_eq_normal hw.symm
    have hck' : flatChkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret labels
        stk₁.length i = some o₁ := by
      rw [flatChkE_eq (good_funcs hg g₁) m₁ l₁]; exact hck
    obtain ⟨ho, inv⟩ := flat_normal (ext := ehExt Γ.tags) hfl (flatChk_of_evalFlat hfl hck')
    have g₂ : Γ.Good s₂ :=
      ⟨(Abstract.XRecursion.evalFlat_funcs hfl).trans g₁.1, TagsOk.evalFlat g₁.2 hfl⟩
    obtain ⟨o', dk, ek⟩ := bwd_cont hg g₂ (inv.2.1.trans m₁) (inv.2.2.trans l₁) (ho ▸ h2) rfl rfl
      ihk
    exact ⟨o', .opOk hi d' hfl dk, ek⟩
  | @opStop s s₁ s₂ f f₁ f₂ big stk₁' i args es fl' hi hargs hflat hfl iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨stk₁, rfl, rfl⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hbk _ hoa
    obtain ⟨fl, hfl₀, rfl⟩ := evalFlat_unwhisk hck hflat
    have hn : ¬ fl.IsNormal := by
      intro h; apply hfl
      rcases fl with _ | _ | _ | _ | _ <;> simp_all [wFl, Flow.IsNormal]
    have hck' : flatChkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret labels
        stk₁.length i = some o₁ := by
      rw [flatChkE_eq (good_funcs hg g₁) m₁ l₁]; exact hck
    obtain ⟨hok, -⟩ := flat_abrupt (ext := ehExt Γ.tags) hfl₀ hn (flatChk_of_evalFlat hfl₀ hck') oc
    exact ⟨_, .opStop hi d' hfl₀ hn, trimO_wFl hok⟩
  | @blockOk s s₁ f f₁ big vs bt body es np nr fl r har hbody hvs hk ihb ihk =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, ho₁⟩ := chk1_blockE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    rw [List.take_append_of_le_length hle] at hbody
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC hbody hg (by rw [hlen]; exact hob)
    have hnr := goodO_blockVals go₁ hob' hvs
    obtain ⟨o', dk, ek⟩ := bwd_cont hg g₁ m₁ l₁ (ho₁ ▸ h2) (len_take_drop hnr hle)
      (take_drop_append hle) ihk
    exact ⟨o', .blockOk har hbody hvs dk, ek⟩
  | @blockBrk s s₁ f f₁ big vs bt body es np nr k har hbody ihb =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, -, -⟩ := chk1_blockE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    rw [List.take_append_of_le_length hle] at hbody
    exact ⟨_, .blockBrk har hbody, rfl⟩
  | @blockEsc s s₁ f f₁ big bt body es np nr o har hbody ho ihb =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, -, -⟩ := chk1_blockE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    rw [List.take_append_of_le_length hle] at hbody
    exact ⟨_, .blockEsc har hbody ho, by rw [whiskO_abrupt (notNormal_of_escapes ho)]⟩
  | @loopOk s s₁ f f₁ big vs bt body es np nr r har hbody hk ihb ihk =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, ho₁⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    rw [List.take_append_of_le_length hle] at hbody
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC hbody hg (by rw [hlen]; exact hob)
    have hnr := (goodO_normal go₁ hob').ge
    obtain ⟨o', dk, ek⟩ := bwd_cont hg g₁ m₁ l₁ (ho₁ ▸ h2) (len_take_drop hnr hle)
      (take_drop_append hle) ihk
    exact ⟨o', .loopOk har hbody dk, ek⟩
  | @loopBack s s₁ f f₁ big vs bt body es np nr r har hbody hk ihb ihk =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, hends, -⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    rw [List.take_append_of_le_length hle] at hbody
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC hbody hg (by rw [hlen]; exact hob)
    have hnp : np ≤ vs.length := by
      obtain ⟨n, hn, hle'⟩ := go₁
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      exact hn ▸ hle'
    have hlen' : (vs.take np ++ stk.drop np).length = stk.length := by
      rw [len_take_drop hnp hle]; omega
    obtain ⟨o', dk, ek⟩ := bwd_cont hg g₁ m₁ l₁ hc hlen' (take_drop_append hle) ihk
    exact ⟨o', .loopBack har hbody dk, ek⟩
  | @loopBrk s s₁ f f₁ big vs bt body es np nr k har hbody ihb =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, -, -⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    rw [List.take_append_of_le_length hle] at hbody
    exact ⟨_, .loopBrk har hbody, rfl⟩
  | @loopEsc s s₁ f f₁ big bt body es np nr o har hbody ho ihb =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨np', nr', hba, hle, -, -⟩ := chk1_loopE h1
    rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    rw [List.take_append_of_le_length hle] at hbody
    exact ⟨_, .loopEsc har hbody ho, by rw [whiskO_abrupt (notNormal_of_escapes ho)]⟩
  | @ifOk s s₁ s₂ f f₁ f₂ big stk₁' vs cv b bt c t el es np nr fl r hc' hb' har harm hvs hk ihc
      iharm ihk =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, hrest⟩ := chk1_ifE h1
    obtain ⟨o, d', e'⟩ := ihc hb hg hcc
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC d' hg hcc
    have hocc : occ = some v.length := go₁
    obtain ⟨np', nr', hba, hle, het, hee, ho₁⟩ := hrest _ hocc
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (by omega)
    rw [← m₁, ← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    have hends : endsAt (chkE (ehExt Γ.tags) s₁.funcs f₁.module f₁.locals.length ret
        (nr :: labels) (some np) (if b then t else el)) nr = true := by
      rw [chk_eq (good_funcs hg g₁) m₁ l₁]; cases b <;> assumption
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    have hle' : np ≤ stk₁.length := by simp at hle; omega
    rw [List.take_append_of_le_length hle'] at harm
    have hlen : (stk₁.take np).length = np := by simp; omega
    obtain ⟨g₂, m₂, l₂, go₂, -⟩ := evalOXP_fwd hC harm g₁ (by rw [hlen]; exact hob)
    have hnr := goodO_blockVals go₂ hob' hvs
    obtain ⟨o', dk, ek⟩ := bwd_cont hg g₂ (m₂.trans m₁) (l₂.trans l₁)
      (by rw [ho₁] at h2; convert h2 using 3; simp) (len_take_drop hnr hle')
      (take_drop_append hle') ihk
    exact ⟨o', .ifOk d' hb' har harm hvs dk, ek⟩
  | @ifBrk s s₁ s₂ f f₁ f₂ big stk₁' vs cv b bt c t el es np nr k hc' hb' har harm ihc iharm =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, hrest⟩ := chk1_ifE h1
    obtain ⟨o, d', e'⟩ := ihc hb hg hcc
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, -, go₁, -⟩ := evalOXP_fwd hC d' hg hcc
    have hocc : occ = some v.length := go₁
    obtain ⟨np', nr', hba, hle, -, -, -⟩ := hrest _ hocc
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (by omega)
    rw [← m₁, ← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    have hle' : np ≤ stk₁.length := by simp at hle; omega
    rw [List.take_append_of_le_length hle'] at harm
    exact ⟨_, .ifBrk d' hb' har harm, rfl⟩
  | @ifEsc s s₁ s₂ f f₁ f₂ big stk₁' cv b bt c t el es np nr o hc' hb' har harm ho ihc iharm =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, hrest⟩ := chk1_ifE h1
    obtain ⟨o', d', e'⟩ := ihc hb hg hcc
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, -, go₁, -⟩ := evalOXP_fwd hC d' hg hcc
    have hocc : occ = some v.length := go₁
    obtain ⟨np', nr', hba, hle, -, -, -⟩ := hrest _ hocc
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (by omega)
    rw [← m₁, ← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at hba
    obtain ⟨rfl, rfl⟩ := hba
    have hle' : np ≤ stk₁.length := by simp at hle; omega
    rw [List.take_append_of_le_length hle'] at harm
    exact ⟨_, .ifEsc d' hb' har harm ho, by rw [whiskO_abrupt (notNormal_of_escapes ho)]⟩
  | ifAbort _ ho ihc =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨occ, hcc, -⟩ := chk1_ifE h1
    obtain ⟨o, d', e'⟩ := ihc hb hg hcc
    exact ⟨o, .ifAbort d' (abrupt_of_trim ho e'), e'⟩
  | @callIndOk s s₁ s₂ f f₁ big stk₁' vs x y args es ad i fa fi ps rs fl r hargs hres hfi hty hy
      hcall hvs hk iha ihk =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some v.length := go₁
    obtain ⟨hp, ho₁⟩ := flatChk_irT (.inl ⟨_, rfl⟩) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callIndirect x y) =
        some o₁ from hbk _ hoa)
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (by omega)
    have hp' : ps.length ≤ stk₁.length := by simp at hp; omega
    rw [List.take_append_of_le_length hp'] at hcall
    obtain ⟨g₂, hlen⟩ := hC _ _ _ _ _ hcall g₁
    have hrs := hlen fi ps rs vs hfi hty hvs
    obtain ⟨o', dk, ek⟩ := bwd_cont hg g₂ m₁ l₁
      (by rw [ho₁] at h2; convert h2 using 3; simp) (len_take_drop hrs hp')
      (take_drop_append hp') ihk
    exact ⟨o', .callIndOk d' hres hfi hty hy hcall hvs dk, ek⟩
  | @callIndRes s s₁ f f₁ big stk₁' x y args es ad i hargs hres iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨-, -, -, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some v.length := go₁
    have h1v := one_le_callIndirect (hbk _ hoa)
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv h1v
    exact ⟨_, .callIndRes d' hres, rfl⟩
  | @callIndStop s s₁ s₂ f f₁ big stk₁' x y args es ad i fa fi ps rs fl hargs hres hfi hty hy
      hcall hfl iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨-, m₁, -, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some v.length := go₁
    obtain ⟨hp, -⟩ := flatChk_irT (.inl ⟨_, rfl⟩) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callIndirect x y) =
        some o₁ from hbk _ hoa)
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (by omega)
    have hp' : ps.length ≤ stk₁.length := by simp at hp; omega
    rw [List.take_append_of_le_length hp'] at hcall
    refine ⟨_, .callIndStop d' hres hfi hty hy hcall hfl, ?_⟩
    rw [whiskO_abrupt (notNormal_of_abrupt hfl)]
  | @callRefOk s s₁ s₂ f f₁ big stk₁' vs y args es fa fi ps rs fl r hargs hfi hty hy hcall hvs hk
      iha ihk =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, h2⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some v.length := go₁
    obtain ⟨hp, ho₁⟩ := flatChk_irT (.inr rfl) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callRef y) =
        some o₁ from hbk _ hoa)
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (by omega)
    have hp' : ps.length ≤ stk₁.length := by simp at hp; omega
    rw [List.take_append_of_le_length hp'] at hcall
    obtain ⟨g₂, hlen⟩ := hC _ _ _ _ _ hcall g₁
    have hrs := hlen fi ps rs vs hfi hty hvs
    obtain ⟨o', dk, ek⟩ := bwd_cont hg g₂ m₁ l₁
      (by rw [ho₁] at h2; convert h2 using 3; simp) (len_take_drop hrs hp')
      (take_drop_append hp') ihk
    exact ⟨o', .callRefOk d' hfi hty hy hcall hvs dk, ek⟩
  | @callRefNull s s₁ f f₁ big stk₁' y args es hargs iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨-, -, -, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some v.length := go₁
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (one_le_callRef (hbk _ hoa))
    exact ⟨_, .callRefNull d', rfl⟩
  | @callRefStop s s₁ s₂ f f₁ big stk₁' y args es fa fi ps rs fl hargs hfi hty hy hcall hfl iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨-, m₁, -, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some v.length := go₁
    obtain ⟨hp, -⟩ := flatChk_irT (.inr rfl) (m₁ ▸ hy)
      (show flatChkE tExt s.funcs f.module f.locals.length ret labels _ (.callRef y) =
        some o₁ from hbk _ hoa)
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (by omega)
    have hp' : ps.length ≤ stk₁.length := by simp at hp; omega
    rw [List.take_append_of_le_length hp'] at hcall
    refine ⟨_, .callRefStop d' hfi hty hy hcall hfl, ?_⟩
    rw [whiskO_abrupt (notNormal_of_abrupt hfl)]
  | @tail s s₁ f f₁ big stk₁' i args es fa fi ps rs hargs hres hfi hty hy iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨stk₁, rfl, rfl⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hbk _ hoa
    rw [flatChkE_eh_tail hres, ← flatChkE_eq (good_funcs hg g₁) m₁ l₁] at hck
    have htp := tailPop_le hres hck
    have hres' := (tailRes_unappend hres htp).1 _ _ rfl
    obtain ⟨hp, -, -⟩ := flatChk_tailForm (tExt_tail hres' hfi hty hy) hck
    refine ⟨_, .tail d' hres' hfi hty hy, ?_⟩
    rw [List.drop_append_of_le_length htp,
      List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
    rfl
  | @tailRes s s₁ f f₁ big stk₁' i args es hargs hres iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨stk₁, rfl, rfl⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hbk _ hoa
    rw [flatChkE_eh_tail hres] at hck
    exact ⟨_, .tailRes d' ((tailRes_unappend hres (tailPop_le hres hck)).2 rfl), rfl⟩
  | @throw s s₁ f f₁ big stk₁' x args es ta ti ts hargs ht he hn iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨stk₁, rfl, rfl⟩ := normal_of_trim e'
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some stk₁.length := go₁
    have hck := hbk _ hoa
    rw [← flatChkE_eq (good_funcs hg g₁) m₁ l₁] at hck
    have hn' := throw_le g₁.2.1 ht he hck
    rw [List.take_append_of_le_length hn']
    exact ⟨_, .throw d' ht he hn', rfl⟩
  | @throwRefNull s s₁ f f₁ big stk₁' args es hargs iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨-, -, -, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some v.length := go₁
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (one_le_throwRef (hbk _ hoa))
    exact ⟨_, .throwRefNull d', rfl⟩
  | @throwRefExn s s₁ f f₁ big stk₁' a args es hargs iha =>
    intro stk rest labels ret oc hb hg hc
    obtain ⟨o₁, h1, -⟩ := chk_consE.mp hc
    obtain ⟨oa, ha, hbk⟩ := chk1_opE h1
    obtain ⟨o, d', e'⟩ := iha hb hg ha
    obtain ⟨v, rfl, hv⟩ := normal_of_trim e'
    obtain ⟨-, -, -, go₁, -⟩ := evalOXP_fwd hC d' hg ha
    have hoa : oa = some v.length := go₁
    obtain ⟨stk₁, rfl, rfl⟩ := cons_of_append hv (one_le_throwRef (hbk _ hoa))
    exact ⟨_, .throwRefExn d', rfl⟩
  | @tryOk s s₁ f f₁ big vs bt cs body es np nr fl r har hbody hvs hk ihb ihk =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨-, -, -, hle, hends, h2⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, hob'⟩ := endsAt_eqE hends
    rw [List.take_append_of_le_length hle] at hbody
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, l₁, go₁, -⟩ := evalOXP_fwd hC hbody hg (by rw [hlen]; exact hob)
    have hnr := goodO_blockVals go₁ hob' hvs
    obtain ⟨o', dk, ek⟩ := bwd_cont hg g₁ m₁ l₁ h2 (len_take_drop hnr hle)
      (take_drop_append hle) ihk
    exact ⟨o', .tryOk har hbody hvs dk, ek⟩
  | @tryBrk s s₁ f f₁ big vs bt cs body es np nr k har hbody ihb =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨-, -, -, hle, -, -⟩ := arity_try_pre har hc
    rw [List.take_append_of_le_length hle] at hbody
    exact ⟨_, .tryBrk har hbody, rfl⟩
  | @tryEsc s s₁ f f₁ big bt cs body es np nr o har hbody ho hnt ihb =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨-, -, -, hle, -, -⟩ := arity_try_pre har hc
    rw [List.take_append_of_le_length hle] at hbody
    exact ⟨_, .tryEsc har hbody ho hnt, by rw [whiskO_abrupt (notNormal_of_escapes ho)]⟩
  | @tryCatch s s₁ f f₁ big us bt cs body es np nr a l har hbody hcs ihb =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨ns, hns, hok, hle, hends, -⟩ := arity_try_pre har hc
    obtain ⟨ob, hob, -⟩ := endsAt_eqE hends
    rw [List.take_append_of_le_length hle] at hbody
    have hlen : (stk.take np).length = np := by simp; omega
    obtain ⟨g₁, m₁, -, -, -⟩ := evalOXP_fwd hC hbody hg (by rw [hlen]; exact hob)
    rw [← m₁] at hns
    obtain ⟨n, hn, hle'⟩ := catches_count g₁.2.2 hcs hns hok
    refine ⟨_, .tryCatch har hbody hcs, ?_⟩
    rw [List.drop_append_of_le_length hle, ← List.append_assoc]
    exact trimO_brk_append ⟨n, hn, by simp; omega⟩
  | @tryRethrow s s₁ f f₁ big bt cs body es np nr a har hbody hcs ihb =>
    intro stk rest labels ret oc hb hg hc
    subst hb
    obtain ⟨-, -, -, hle, -, -⟩ := arity_try_pre har hc
    rw [List.take_append_of_le_length hle] at hbody
    exact ⟨_, .tryRethrow har hbody hcs, rfl⟩

end Silmaril.Proofs.Wasm.Abstract.ExposePTyped
