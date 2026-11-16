module

public import Silmaril.Wasm.Abstract.TypedCat.Defs
public import Silmaril.Wasm.Abstract.CallXP.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCat.Thms`: **the answered runs of a sequence compose**
(`evalOXP_append_iff`): a run of `es₁ ++ es₂` is a run of `es₁` falling through and then a run of
`es₂`, or a run of `es₁` not falling through (a branch, a return, a trap, an exception or a
pending tail call), which skips `es₂`. Both directions by induction on the derivation; a `loop`
continuing (`loopBack`) re-enters the same sequence.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.TypedCat

variable {H : Type} {C : Abstract.CallRel H}

theorem notNormal_of_escapes' {o : POut} (h : o.Escapes) : ¬ o.IsNormal := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    simp_all [POut.Escapes, POut.IsNormal, Flow.Escapes, Flow.IsNormal]

theorem notNormal_of_abrupt' {fl : Flow} (h : fl.Abrupt) : ¬ (POut.flow fl).IsNormal := by
  rcases fl with _ | _ | _ | _ | _ <;> simp_all [POut.IsNormal, Flow.IsNormal, Flow.Abrupt]

/-- The decomposition of a run of `es₁ ++ es₂`. -/
def SeqD (C : Abstract.CallRel H) (s : Store H) (f : Frame) (stk : List Val)
    (es₁ es₂ : List BExpr) (r : Store H × Frame × POut) : Prop :=
  (∃ s₁ f₁ vs, EvalOXP C s f stk es₁ (s₁, f₁, .flow (.normal vs)) ∧ EvalOXP C s₁ f₁ vs es₂ r) ∨
    (EvalOXP C s f stk es₁ r ∧ ¬ r.2.2.IsNormal)

section Split

variable {es₂ : List BExpr}

theorem cons_case {e : BExpr} {es : List BExpr} {P : List BExpr → Prop}
    (hP : ∀ es₁, es = es₁ ++ es₂ → P (e :: es₁)) :
    ∀ es₁, e :: es = es₁ ++ es₂ → es₁ = [] ∨ P es₁ := by
  intro es₁ hL
  cases es₁ with
  | nil => exact .inl rfl
  | cons e' es₁ =>
    simp only [List.cons_append, List.cons.injEq] at hL
    obtain ⟨rfl, rfl⟩ := hL
    exact .inr (hP es₁ rfl)

theorem cont_split {s s' : Store H} {f f' : Frame} {stk stk' : List Val} {e : BExpr}
    {es₁ : List BExpr} {r : Store H × Frame × POut}
    (K : ∀ {es : List BExpr} {r : Store H × Frame × POut}, EvalOXP C s' f' stk' es r →
      EvalOXP C s f stk (e :: es) r)
    (hk : EvalOXP C s' f' stk' (es₁ ++ es₂) r) (ih : es₁ = [] ∨ SeqD C s' f' stk' es₁ es₂ r) :
    SeqD C s f stk (e :: es₁) es₂ r := by
  rcases ih with rfl | ⟨s₁, f₁, vs, h₁, h₂⟩ | ⟨h₁, hn⟩
  · exact .inl ⟨s', f', stk', K .nil, hk⟩
  · exact .inl ⟨s₁, f₁, vs, K h₁, h₂⟩
  · exact .inr ⟨K h₁, hn⟩

theorem back_split {s s' : Store H} {f f' : Frame} {stk stk' : List Val} {e : BExpr}
    {es₁ : List BExpr} {r : Store H × Frame × POut}
    (K : ∀ {r : Store H × Frame × POut}, EvalOXP C s' f' stk' (e :: es₁) r →
      EvalOXP C s f stk (e :: es₁) r)
    (ih : e :: es₁ = [] ∨ SeqD C s' f' stk' (e :: es₁) es₂ r) :
    SeqD C s f stk (e :: es₁) es₂ r := by
  rcases ih with h | ⟨s₁, f₁, vs, h₁, h₂⟩ | ⟨h₁, hn⟩
  · cases h
  · exact .inl ⟨s₁, f₁, vs, K h₁, h₂⟩
  · exact .inr ⟨K h₁, hn⟩

/-- **A run of `es₁ ++ es₂` splits** (for `es₁ ≠ []`). -/
theorem split_aux {s : Store H} {f : Frame} {stk : List Val} {L : List BExpr}
    {r : Store H × Frame × POut} (h : EvalOXP C s f stk L r) :
    ∀ es₁, L = es₁ ++ es₂ → es₁ = [] ∨ SeqD C s f stk es₁ es₂ r := by
  induction h with
  | nil =>
    intro es₁ hL
    cases es₁ with
    | nil => exact .inl rfl
    | cons => simp at hL
  | argsAbort hargs ho _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.argsAbort hargs ho, ho⟩
  | callOk hargs hfi hty hcall hvs hk _ ih =>
    exact cons_case fun es₁ hes => by
      subst hes; exact cont_split (fun h => .callOk hargs hfi hty hcall hvs h) hk (ih es₁ rfl)
  | callTrap hargs hfi hty hcall _ =>
    exact cons_case fun es₁ hes => by
      subst hes; exact .inr ⟨.callTrap hargs hfi hty hcall, fun h => h⟩
  | callThrow hargs hfi hty hcall _ =>
    exact cons_case fun es₁ hes => by
      subst hes; exact .inr ⟨.callThrow hargs hfi hty hcall, fun h => h⟩
  | opOk hi hargs hflat hk _ ih =>
    exact cons_case fun es₁ hes => by
      subst hes; exact cont_split (fun h => .opOk hi hargs hflat h) hk (ih es₁ rfl)
  | opStop hi hargs hflat hfl _ =>
    exact cons_case fun es₁ hes => by
      subst hes; exact .inr ⟨.opStop hi hargs hflat hfl, hfl⟩
  | blockOk har hbody hvs hk _ ih =>
    exact cons_case fun es₁ hes => by
      subst hes; exact cont_split (fun h => .blockOk har hbody hvs h) hk (ih es₁ rfl)
  | blockBrk har hbody _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.blockBrk har hbody, fun h => h⟩
  | blockEsc har hbody ho _ =>
    exact cons_case fun es₁ hes => by
      subst hes; exact .inr ⟨.blockEsc har hbody ho, notNormal_of_escapes' ho⟩
  | loopOk har hbody hk _ ih =>
    exact cons_case fun es₁ hes => by
      subst hes; exact cont_split (fun h => .loopOk har hbody h) hk (ih es₁ rfl)
  | loopBack har hbody hk _ ih =>
    exact cons_case fun es₁ hes => by
      subst hes; exact back_split (fun h => .loopBack har hbody h) (ih _ rfl)
  | loopBrk har hbody _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.loopBrk har hbody, fun h => h⟩
  | loopEsc har hbody ho _ =>
    exact cons_case fun es₁ hes => by
      subst hes; exact .inr ⟨.loopEsc har hbody ho, notNormal_of_escapes' ho⟩
  | ifOk hc hb har harm hvs hk _ _ ih =>
    exact cons_case fun es₁ hes => by
      subst hes; exact cont_split (fun h => .ifOk hc hb har harm hvs h) hk (ih es₁ rfl)
  | ifBrk hc hb har harm _ _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.ifBrk hc hb har harm, fun h => h⟩
  | ifEsc hc hb har harm ho _ _ =>
    exact cons_case fun es₁ hes => by
      subst hes; exact .inr ⟨.ifEsc hc hb har harm ho, notNormal_of_escapes' ho⟩
  | ifAbort hc ho _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.ifAbort hc ho, ho⟩
  | callIndOk hargs hres hfi hty hy hcall hvs hk _ ih =>
    exact cons_case fun es₁ hes => by
      subst hes
      exact cont_split (fun h => .callIndOk hargs hres hfi hty hy hcall hvs h) hk (ih es₁ rfl)
  | callIndRes hargs hres _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.callIndRes hargs hres, fun h => h⟩
  | callIndStop hargs hres hfi hty hy hcall hfl _ =>
    exact cons_case fun es₁ hes => by
      subst hes
      exact .inr ⟨.callIndStop hargs hres hfi hty hy hcall hfl, notNormal_of_abrupt' hfl⟩
  | callRefOk hargs hfi hty hy hcall hvs hk _ ih =>
    exact cons_case fun es₁ hes => by
      subst hes
      exact cont_split (fun h => .callRefOk hargs hfi hty hy hcall hvs h) hk (ih es₁ rfl)
  | callRefNull hargs _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.callRefNull hargs, fun h => h⟩
  | callRefStop hargs hfi hty hy hcall hfl _ =>
    exact cons_case fun es₁ hes => by
      subst hes
      exact .inr ⟨.callRefStop hargs hfi hty hy hcall hfl, notNormal_of_abrupt' hfl⟩
  | tail hargs hres hfi hty hy _ =>
    exact cons_case fun es₁ hes => by
      subst hes; exact .inr ⟨.tail hargs hres hfi hty hy, fun h => h⟩
  | tailRes hargs hres _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.tailRes hargs hres, fun h => h⟩
  | throw hargs ht he hn _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.throw hargs ht he hn, fun h => h⟩
  | throwRefNull hargs _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.throwRefNull hargs, fun h => h⟩
  | throwRefExn hargs _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.throwRefExn hargs, fun h => h⟩
  | tryOk har hbody hvs hk _ ih =>
    exact cons_case fun es₁ hes => by
      subst hes; exact cont_split (fun h => .tryOk har hbody hvs h) hk (ih es₁ rfl)
  | tryBrk har hbody _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.tryBrk har hbody, fun h => h⟩
  | tryEsc har hbody ho hnt _ =>
    exact cons_case fun es₁ hes => by
      subst hes; exact .inr ⟨.tryEsc har hbody ho hnt, notNormal_of_escapes' ho⟩
  | tryCatch har hbody hc _ =>
    exact cons_case fun es₁ hes => by subst hes; exact .inr ⟨.tryCatch har hbody hc, fun h => h⟩
  | tryRethrow har hbody hc _ =>
    exact cons_case fun es₁ hes => by
      subst hes; exact .inr ⟨.tryRethrow har hbody hc, fun h => h⟩

end Split

/-- **A run of `es₁` continues into `es₂`.** -/
theorem compose_aux {s : Store H} {f : Frame} {stk : List Val} {es₁ : List BExpr}
    {r₁ : Store H × Frame × POut} (h : EvalOXP C s f stk es₁ r₁) :
    ∀ {es₂ : List BExpr} {r : Store H × Frame × POut},
      (∀ vs, r₁.2.2 = .flow (.normal vs) → EvalOXP C r₁.1 r₁.2.1 vs es₂ r) →
      (¬ r₁.2.2.IsNormal → r = r₁) → EvalOXP C s f stk (es₁ ++ es₂) r := by
  induction h with
  | nil => intro es₂ r h1 _; exact h1 _ rfl
  | argsAbort hargs ho _ => intro es₂ r _ h2; rw [h2 ho]; exact .argsAbort hargs ho
  | callOk hargs hfi hty hcall hvs _ _ ih =>
    intro es₂ r h1 h2; exact .callOk hargs hfi hty hcall hvs (ih h1 h2)
  | callTrap hargs hfi hty hcall _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .callTrap hargs hfi hty hcall
  | callThrow hargs hfi hty hcall _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .callThrow hargs hfi hty hcall
  | opOk hi hargs hflat _ _ ih =>
    intro es₂ r h1 h2; exact .opOk hi hargs hflat (ih h1 h2)
  | opStop hi hargs hflat hfl _ =>
    intro es₂ r _ h2; rw [h2 hfl]; exact .opStop hi hargs hflat hfl
  | blockOk har hbody hvs _ _ ih =>
    intro es₂ r h1 h2; exact .blockOk har hbody hvs (ih h1 h2)
  | blockBrk har hbody _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .blockBrk har hbody
  | blockEsc har hbody ho _ =>
    intro es₂ r _ h2; rw [h2 (notNormal_of_escapes' ho)]; exact .blockEsc har hbody ho
  | loopOk har hbody _ _ ih =>
    intro es₂ r h1 h2; exact .loopOk har hbody (ih h1 h2)
  | loopBack har hbody _ _ ih =>
    intro es₂ r h1 h2; exact .loopBack har hbody (ih h1 h2)
  | loopBrk har hbody _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .loopBrk har hbody
  | loopEsc har hbody ho _ =>
    intro es₂ r _ h2; rw [h2 (notNormal_of_escapes' ho)]; exact .loopEsc har hbody ho
  | ifOk hc hb har harm hvs _ _ _ ih =>
    intro es₂ r h1 h2; exact .ifOk hc hb har harm hvs (ih h1 h2)
  | ifBrk hc hb har harm _ _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .ifBrk hc hb har harm
  | ifEsc hc hb har harm ho _ _ =>
    intro es₂ r _ h2; rw [h2 (notNormal_of_escapes' ho)]; exact .ifEsc hc hb har harm ho
  | ifAbort hc ho _ =>
    intro es₂ r _ h2; rw [h2 ho]; exact .ifAbort hc ho
  | callIndOk hargs hres hfi hty hy hcall hvs _ _ ih =>
    intro es₂ r h1 h2; exact .callIndOk hargs hres hfi hty hy hcall hvs (ih h1 h2)
  | callIndRes hargs hres _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .callIndRes hargs hres
  | callIndStop hargs hres hfi hty hy hcall hfl _ =>
    intro es₂ r _ h2; rw [h2 (notNormal_of_abrupt' hfl)]
    exact .callIndStop hargs hres hfi hty hy hcall hfl
  | callRefOk hargs hfi hty hy hcall hvs _ _ ih =>
    intro es₂ r h1 h2; exact .callRefOk hargs hfi hty hy hcall hvs (ih h1 h2)
  | callRefNull hargs _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .callRefNull hargs
  | callRefStop hargs hfi hty hy hcall hfl _ =>
    intro es₂ r _ h2; rw [h2 (notNormal_of_abrupt' hfl)]
    exact .callRefStop hargs hfi hty hy hcall hfl
  | tail hargs hres hfi hty hy _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .tail hargs hres hfi hty hy
  | tailRes hargs hres _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .tailRes hargs hres
  | throw hargs ht he hn _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .throw hargs ht he hn
  | throwRefNull hargs _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .throwRefNull hargs
  | throwRefExn hargs _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .throwRefExn hargs
  | tryOk har hbody hvs _ _ ih =>
    intro es₂ r h1 h2; exact .tryOk har hbody hvs (ih h1 h2)
  | tryBrk har hbody _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .tryBrk har hbody
  | tryEsc har hbody ho hnt _ =>
    intro es₂ r _ h2; rw [h2 (notNormal_of_escapes' ho)]; exact .tryEsc har hbody ho hnt
  | tryCatch har hbody hc _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .tryCatch har hbody hc
  | tryRethrow har hbody hc _ =>
    intro es₂ r _ h2; rw [h2 (fun h => h)]; exact .tryRethrow har hbody hc

/-- **The answered runs of a sequence compose.** -/
theorem evalOXP_append_iff {s : Store H} {f : Frame} {stk : List Val} {es₁ es₂ : List BExpr}
    {r : Store H × Frame × POut} :
    EvalOXP C s f stk (es₁ ++ es₂) r ↔ SeqD C s f stk es₁ es₂ r := by
  constructor
  · intro h
    rcases split_aux h es₁ rfl with rfl | hd
    · exact .inl ⟨s, f, stk, .nil, h⟩
    · exact hd
  · rintro (⟨s₁, f₁, vs, h₁, h₂⟩ | ⟨h₁, hn⟩)
    · refine compose_aux h₁ (fun vs' hv => ?_) (fun hn => absurd trivial hn)
      simp only [POut.flow.injEq, Flow.normal.injEq] at hv
      subst hv; exact h₂
    · exact compose_aux h₁ (fun vs hv => absurd (by rw [hv]; trivial) hn) (fun _ => rfl)

end Silmaril.Proofs.Wasm.Abstract.TypedCat
