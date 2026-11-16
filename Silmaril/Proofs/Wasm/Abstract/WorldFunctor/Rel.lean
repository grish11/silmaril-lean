module

public import Silmaril.Wasm.Abstract.WorldFunctor.Defs
public import Silmaril.Wasm.Abstract.TypedFunctor.Thms
public import Silmaril.Wasm.Abstract.TypedCat.Thms
public import Silmaril.Wasm.Abstract.ExposeP.Thms

/-!
Proofs for `Silmaril.Wasm.Abstract.WorldFunctor.Thms`: trap forgetting, restriction, the
iteration of relations and the loop, and answering the exit-monad denotation.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.WorldFunctor

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposePTyped Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.TypedFunctor Silmaril.Wasm.Abstract.WorldFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)

variable {H : Type}

/-! ## Trap forgetting -/

theorem trapR_ne {g : ORel H} {s : Store H} {f : Frame} {stk : List Val} {s' : Store H}
    {f' : Frame} {o : POut} (ho : o ≠ .flow .trap) :
    trapR g s f stk s' f' o ↔ g s f stk s' f' o := by
  rcases o with (_ | _ | _ | _ | _) | _ <;> first | exact Iff.rfl | exact absurd rfl ho

theorem trapR_trap {g : ORel H} {s : Store H} {f : Frame} {stk : List Val} {s' : Store H}
    {f' : Frame} : trapR g s f stk s' f' (.flow .trap) ↔ ∃ s'' f'', g s f stk s'' f'' (.flow .trap) :=
  Iff.rfl

theorem not_isNormal_trap : ¬ (POut.flow .trap).IsNormal := fun h => h

theorem trapR_seqR (g₁ g₂ : ORel H) : trapR (seqR g₁ g₂) = seqR (trapR g₁) (trapR g₂) := by
  funext s f stk s' f' o
  apply propext
  by_cases ho : o = .flow .trap
  · subst ho
    rw [trapR_trap]
    constructor
    · rintro ⟨s'', f'', (⟨s₁, f₁, vs, h₁, h₂⟩ | ⟨h₁, -⟩)⟩
      · exact .inl ⟨s₁, f₁, vs, h₁, ⟨s'', f'', h₂⟩⟩
      · exact .inr ⟨⟨s'', f'', h₁⟩, not_isNormal_trap⟩
    · rintro (⟨s₁, f₁, vs, h₁, ⟨s'', f'', h₂⟩⟩ | ⟨⟨s'', f'', h₁⟩, -⟩)
      · exact ⟨s'', f'', .inl ⟨s₁, f₁, vs, h₁, h₂⟩⟩
      · exact ⟨s'', f'', .inr ⟨h₁, not_isNormal_trap⟩⟩
  · rw [trapR_ne ho]
    unfold seqR
    rw [trapR_ne ho]
    constructor
    · rintro (⟨a, b, c, h₁, h₂⟩ | h)
      · exact .inl ⟨a, b, c, h₁, (trapR_ne ho).2 h₂⟩
      · exact .inr h
    · rintro (⟨a, b, c, h₁, h₂⟩ | h)
      · exact .inl ⟨a, b, c, h₁, (trapR_ne ho).1 h₂⟩
      · exact .inr h

theorem trapR_idR : trapR (idR : ORel H) = idR := by
  funext s f stk s' f' o
  apply propext
  by_cases ho : o = .flow .trap
  · subst ho
    rw [trapR_trap]
    constructor
    · rintro ⟨_, _, -, -, h⟩; cases h
    · rintro ⟨-, -, h⟩; cases h
  · exact trapR_ne ho

/-- `trapR g` is trap-closed. -/
theorem trapR_trap_closed (g : ORel H) {s : Store H} {f : Frame} {stk : List Val} {s' : Store H}
    {f' : Frame} (s'' : Store H) (f'' : Frame) (h : trapR g s f stk s' f' (.flow .trap)) :
    trapR g s f stk s'' f'' (.flow .trap) := h

/-- A trap-closed relation is its own trap forgetting. -/
theorem trapR_of_closed {g : ORel H}
    (hg : ∀ s f stk s' f' s'' f'', g s f stk s' f' (.flow .trap) → g s f stk s'' f'' (.flow .trap)) :
    trapR g = g := by
  funext s f stk s' f' o
  apply propext
  by_cases ho : o = .flow .trap
  · subst ho
    rw [trapR_trap]
    exact ⟨fun ⟨_, _, h⟩ => hg _ _ _ _ _ _ _ h, fun h => ⟨_, _, h⟩⟩
  · exact trapR_ne ho

theorem trapR_resR (P : Store H → Frame → List Val → Prop) (g : ORel H) :
    trapR (resR P g) = resR P (trapR g) := by
  funext s f stk s' f' o
  apply propext
  by_cases ho : o = .flow .trap
  · subst ho
    exact ⟨fun ⟨a, b, hp, h⟩ => ⟨hp, a, b, h⟩, fun ⟨hp, a, b, h⟩ => ⟨a, b, hp, h⟩⟩
  · unfold resR; rw [trapR_ne ho, trapR_ne ho]

/-! ## Restriction -/

theorem resR_seqR (P : Store H → Frame → List Val → Prop) (g₁ g₂ : ORel H) :
    resR P (seqR g₁ g₂) = seqR (resR P g₁) g₂ := by
  funext s f stk s' f' o
  apply propext
  constructor
  · rintro ⟨hp, ⟨s₁, f₁, vs, h₁, h₂⟩ | ⟨h₁, hn⟩⟩
    · exact .inl ⟨s₁, f₁, vs, ⟨hp, h₁⟩, h₂⟩
    · exact .inr ⟨⟨hp, h₁⟩, hn⟩
  · rintro (⟨s₁, f₁, vs, ⟨hp, h₁⟩, h₂⟩ | ⟨⟨hp, h₁⟩, hn⟩)
    · exact ⟨hp, .inl ⟨s₁, f₁, vs, h₁, h₂⟩⟩
    · exact ⟨hp, .inr ⟨h₁, hn⟩⟩

theorem seqR_resR_of_lands {Q : Store H → Frame → List Val → Prop} {g₁ : ORel H} (g₂ : ORel H)
    (hl : ∀ s f stk s' f' vs, g₁ s f stk s' f' (.flow (.normal vs)) → Q s' f' vs) :
    seqR g₁ (resR Q g₂) = seqR g₁ g₂ := by
  funext s f stk s' f' o
  apply propext
  constructor
  · rintro (⟨s₁, f₁, vs, h₁, -, h₂⟩ | h)
    · exact .inl ⟨s₁, f₁, vs, h₁, h₂⟩
    · exact .inr h
  · rintro (⟨s₁, f₁, vs, h₁, h₂⟩ | h)
    · exact .inl ⟨s₁, f₁, vs, h₁, hl _ _ _ _ _ _ h₁, h₂⟩
    · exact .inr h

theorem resR_of_supp {P : Store H → Frame → List Val → Prop} {g : ORel H}
    (hs : ∀ s f stk s' f' o, g s f stk s' f' o → P s f stk) : resR P g = g := by
  funext s f stk s' f' o
  exact propext ⟨fun h => h.2, fun h => ⟨hs _ _ _ _ _ _ h, h⟩⟩

theorem seqR_resR_idR_left (P : Store H → Frame → List Val → Prop) {g : ORel H}
    (hs : ∀ s f stk s' f' o, g s f stk s' f' o → P s f stk) : seqR (resR P idR) g = g := by
  rw [← resR_seqR, seqR_idR_left, resR_of_supp hs]

theorem seqR_resR_idR_right (Q : Store H → Frame → List Val → Prop) {g : ORel H}
    (hl : ∀ s f stk s' f' vs, g s f stk s' f' (.flow (.normal vs)) → Q s' f' vs) :
    seqR g (resR Q idR) = g := by
  rw [seqR_resR_of_lands _ hl, seqR_idR_right]

/-! ## Iteration -/

theorem iterR_iff (F : LStep H) {s : Store H} {f : Frame} {stk : List Val} {s' : Store H}
    {f' : Frame} {o : POut} : iterR F s f stk s' f' o ↔ unfoldR F (iterR F) s f stk s' f' o := by
  constructor
  · rintro (h | ⟨h₁, h₂⟩)
    · exact .inl h
    · exact .inr ⟨_, _, _, h₁, h₂⟩
  · rintro (h | ⟨_, _, _, h₁, h₂⟩)
    · exact .done h
    · exact .back h₁ h₂

theorem iterR_least (F : LStep H) {g : ORel H}
    (hg : ∀ s f stk s' f' o, unfoldR F g s f stk s' f' o → g s f stk s' f' o) :
    ∀ s f stk s' f' o, iterR F s f stk s' f' o → g s f stk s' f' o := by
  intro s f stk s' f' o h
  induction h with
  | done h => exact hg _ _ _ _ _ _ (.inl h)
  | back h₁ _ ih => exact hg _ _ _ _ _ _ (.inr ⟨_, _, _, h₁, ih⟩)

/-! ## The loop -/

theorem loopOutR_esc {np nr : Nat} {stk : List Val} {o : POut} (ho : o.Escapes) :
    loopOutR np nr stk o = .inl o := by
  rcases o with (_ | _ | _ | _ | _) | _ <;> first | rfl | exact absurd ho id

theorem iterR_of_evalOXP {C : Abstract.CallRel H} {bt : BlockType} {body : List BExpr}
    {s : Store H} {f : Frame} {stk : List Val} {L : List BExpr} {r : Store H × Frame × POut}
    (h : EvalOXP C s f stk L r) :
    L = [.loop bt body] → iterR (loopStepR C bt body) s f stk r.1 r.2.1 r.2.2 := by
  induction h with
  | loopOk har hb hk _ _ =>
    intro hL; cases hL
    cases hk
    exact .done ⟨_, _, _, har, hb, rfl⟩
  | loopBack har hb _ _ ih =>
    intro hL; cases hL
    exact .back ⟨_, _, _, har, hb, rfl⟩ (ih rfl)
  | loopBrk har hb =>
    intro hL; cases hL
    exact .done ⟨_, _, _, har, hb, rfl⟩
  | loopEsc har hb ho =>
    intro hL; cases hL
    exact .done ⟨_, _, _, har, hb, (loopOutR_esc ho).symm⟩
  | _ => intro hL; cases hL

theorem evalOXP_of_iterR {C : Abstract.CallRel H} {bt : BlockType} {body : List BExpr}
    {s : Store H} {f : Frame} {stk : List Val} {s' : Store H} {f' : Frame} {o : POut}
    (h : iterR (loopStepR C bt body) s f stk s' f' o) :
    EvalOXP C s f stk [.loop bt body] (s', f', o) := by
  induction h with
  | done h =>
    obtain ⟨np, nr, o', har, hb, hx⟩ := h
    rcases o' with ((vs | ⟨_ | k, vs⟩ | vs | _ | a) | ⟨a, args, n⟩) <;>
      simp only [loopOutR, Sum.inl.injEq, reduceCtorEq] at hx <;> subst hx
    · exact .loopOk har hb .nil
    · exact .loopBrk har hb
    · exact .loopEsc har hb trivial
    · exact .loopEsc har hb trivial
    · exact .loopEsc har hb trivial
    · exact .loopEsc har hb trivial
  | back h _ ih =>
    obtain ⟨np, nr, o', har, hb, hx⟩ := h
    rcases o' with ((vs | ⟨_ | k, vs⟩ | vs | _ | a) | ⟨a, args, n⟩) <;>
      simp only [loopOutR, Sum.inr.injEq, reduceCtorEq] at hx
    subst hx
    exact .loopBack har hb ih

theorem denR_loop (C : Abstract.CallRel H) (bt : BlockType) (body : List BExpr) :
    denR C [.loop bt body] = iterR (loopStepR C bt body) := by
  funext s f stk s' f' o
  exact propext ⟨fun h => iterR_of_evalOXP h rfl, evalOXP_of_iterR⟩

/-! ## Answering the exit-monad denotation -/

theorem ans_denK (C : Abstract.CallRel H) (es : List BExpr) :
    Ans C (denK es) = trapR (denR C es) := by
  funext s f stk s' f' o
  apply propext
  unfold Ans
  rw [← denL_eq_ofK]
  by_cases ho : o = .flow .trap
  · subst ho
    rw [trapR_trap]
    exact evalOXP_trap_iff.symm
  · rw [trapR_ne ho]
    have he : ansEnd s' f' o = .val (.ok (⟨(f', o)⟩, ⟨s'⟩)) := by
      rcases o with (_ | _ | _ | _ | _) | _ <;> first | rfl | exact absurd rfl ho
    rw [he]
    exact (evalOXP_iff ho).symm

end Silmaril.Proofs.Wasm.Abstract.WorldFunctor
