module

public import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Flat
public import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Tensor

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePStruct.Thms`: the stack tensor on a checked
stack-pure operator, and on a continuation after code with the result invariant `GoodR`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.Body
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.ExposeE
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Interp

variable {H : Type}

/-! ## Results -/

/-- Append `rest` to every stack a body result carries. -/
def wP (rest : List Val) : ResP → ResP
  | ⟨(f, .flow fl)⟩ => ⟨(f, .flow (wFl rest fl))⟩
  | r => r

/-- A body result that is not a fallthrough. -/
def NotNormal (r : ResP) : Prop := ∀ f vs, r ≠ ⟨(f, .flow (.normal vs))⟩

theorem whiskP_notNormal {rest : List Val} {r : ResP} (h : NotNormal r) : whiskP rest r = r := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal vs => exact absurd rfl (h f vs)
    | _ => rfl
  · rfl

theorem trimP_normal (labels : List Nat) (ret : Nat) (f : Frame) (vs : List Val) :
    trimP labels ret ⟨(f, .flow (.normal vs))⟩ = ⟨(f, .flow (.normal vs))⟩ := rfl

theorem trimP_notNormal {labels : List Nat} {ret : Nat} {r : ResP} (h : NotNormal r) :
    NotNormal (trimP labels ret r) := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal vs => exact absurd rfl (h f vs)
    | _ => intro f' vs' he; simp [trimP] at he
  · intro f' vs' he; simp [trimP] at he

theorem normal_or (r : ResP) : (∃ f vs, r = ⟨(f, .flow (.normal vs))⟩) ∨ NotNormal r := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal vs => exact .inl ⟨f, vs, rfl⟩
    | _ => exact .inr fun f' vs' he => by simp at he
  · exact .inr fun f' vs' he => by simp at he

theorem goodR_notNormal {env : Env} {o o' : Option Nat} {r : ResP} (h : NotNormal r)
    (hg : GoodR env o r) : GoodR env o' r := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal vs => exact absurd rfl (h f vs)
    | _ => exact hg
  · exact hg

theorem goodR_none_notNormal {env : Env} {r : ResP} (hg : GoodR env none r) : NotNormal r := by
  rintro f vs rfl
  simp [GoodR] at hg

theorem trim_wP {env : Env} {o : Option Nat} {r : ResP} (rest : List Val) (hg : GoodR env o r) :
    trimP env.labels env.ret (wP rest r) = trimP env.labels env.ret (whiskP rest r) := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | brk l vs =>
      obtain ⟨-, n, hn, hle⟩ := hg
      simp only [wP, wFl, whiskP, trimP, hn, List.take_append_of_le_length hle]
    | ret vs =>
      obtain ⟨-, hle⟩ := hg
      simp only [wP, wFl, whiskP, trimP, List.take_append_of_le_length hle]
    | _ => rfl
  · rfl

/-! ## Continuations -/

/-- Read `K` through `trimP` after a fallthrough; every other result passes. -/
noncomputable def kn (labels : List Nat) (ret : Nat) (K : ResP → M (CallSig H) H ResP) :
    ResP → M (CallSig H) H ResP
  | ⟨(f, .flow (.normal vs))⟩ => obsP labels ret (K ⟨(f, .flow (.normal vs))⟩)
  | r => pure r

theorem kn_trim {labels : List Nat} {ret : Nat} {K : ResP → M (CallSig H) H ResP}
    (hK : ∀ r, NotNormal r → K r = pure r) (r : ResP) :
    (K r >>= fun r => pure (trimP labels ret r)) = kn labels ret K (trimP labels ret r) := by
  rcases normal_or r with ⟨f, vs, rfl⟩ | hr
  · rfl
  · rw [hK r hr, pure_bind]
    have h2 := trimP_notNormal (labels := labels) (ret := ret) hr
    revert h2
    generalize trimP labels ret r = t
    intro h2
    rcases normal_or t with ⟨f, vs, rfl⟩ | _
    · exact absurd rfl (h2 f vs)
    · rcases t with ⟨f, (fl | ⟨a, args, n⟩)⟩
      · cases fl with
        | normal vs => exact absurd rfl (h2 f vs)
        | _ => rfl
      · rfl

/-- **The tensor through a continuation.** If `x'` is `x` with `rest` below (read through
`trimP`), `x` lands in `GoodR env o₁`, `K` passes every result but a fallthrough, and `K` on a
fallthrough of height `o₁` commutes with the tensor, so does `x >>= K`. -/
theorem cont_whisk {env : Env} {o₁ : Option Nat} {x x' : M (CallSig H) H ResP}
    {K : ResP → M (CallSig H) H ResP} (rest : List Val) (hx : Lands (GoodR env o₁) x)
    (hxw : obsP env.labels env.ret x' =
      x >>= fun r => pure (trimP env.labels env.ret (whiskP rest r)))
    (hK : ∀ r, NotNormal r → K r = pure r)
    (hk : ∀ f vs, f.module = env.mi → o₁ = some vs.length →
      obsP env.labels env.ret (K ⟨(f, .flow (.normal (vs ++ rest)))⟩) =
        K ⟨(f, .flow (.normal vs))⟩ >>= fun r => pure (trimP env.labels env.ret (whiskP rest r))) :
    obsP env.labels env.ret (x' >>= K) =
      (x >>= K) >>= fun r => pure (trimP env.labels env.ret (whiskP rest r)) := by
  have e1 : obsP env.labels env.ret (x' >>= K) =
      obsP env.labels env.ret x' >>= kn env.labels env.ret K := by
    simp only [obsP, bind_assoc, pure_bind]
    congr 1
    funext r
    exact kn_trim hK r
  rw [e1, hxw, bind_assoc, bind_assoc]
  refine bind_congr_lands hx fun r hr => ?_
  rw [pure_bind]
  rcases normal_or r with ⟨f, vs, rfl⟩ | hn
  · exact hk f vs hr.1 hr.2
  · rw [whiskP_notNormal hn, hK r hn, pure_bind]
    rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
    · cases fl with
      | normal vs => exact absurd rfl (hn f vs)
      | _ => rfl
    · rfl

theorem cont_lands {env : Env} {o₁ o : Option Nat} {x : M (CallSig H) H ResP}
    {K : ResP → M (CallSig H) H ResP} (hx : Lands (GoodR env o₁) x)
    (hK : ∀ r, NotNormal r → K r = pure r)
    (hk : ∀ f vs, f.module = env.mi → o₁ = some vs.length →
      Lands (GoodR env o) (K ⟨(f, .flow (.normal vs))⟩)) :
    Lands (GoodR env o) (x >>= K) := by
  refine lands_bind hx fun r hr => ?_
  rcases normal_or r with ⟨f, vs, rfl⟩ | hn
  · exact hk f vs hr.1 hr.2
  · rw [hK r hn]; exact lands_pure (goodR_notNormal hn hr)

theorem thenKP_notNormal (k : Frame → List Val → M (CallSig H) H ResP) (r : ResP)
    (h : NotNormal r) : thenKP k r = pure r := by
  rcases resP_cases (H := H) r with ⟨f, vs, rfl⟩ | hp
  · exact absurd rfl (h f vs)
  · exact hp k

theorem ifKP_notNormal (bt : BlockType) (gt ge : PHom H Cfg ResP) (r : ResP)
    (h : NotNormal r) : ifKP bt gt ge r = pure r := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal vs => exact absurd rfl (h f vs)
    | _ => rfl
  · rfl

/-! ## Operators -/

/-- Flat instructions keep the frame's instance. -/
theorem evalFlat_module' {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr}
    {fl : Flow} (h : evalFlat s f stk i = some (s', f', fl)) : f'.module = f.module := by
  unfold evalFlat at h
  repeat' (first | split at h | (simp only [Option.map_eq_some_iff, Option.bind_eq_bind,
    Option.bind_eq_some_iff] at h))
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h; obtain ⟨-, rfl, -⟩ := h; rfl)
    | (obtain ⟨_, -, h⟩ := h; simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl, -⟩ := h; rfl)
    | (simp at h; done)
    | (obtain ⟨_, -, _, -, -, rfl, -⟩ := h; rfl)
    | (obtain ⟨a, -, b, -, h⟩ := h
       split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; rfl))

theorem opCXP_flat {i : Instr} (hp : instrStackPure i = true) (hne : i ≠ .throwRef) (f : Frame)
    (stk : List Val) : opCXP (H := H) i f stk = liftP (flatK i f stk) := by
  cases i <;> first | rfl | exact absurd rfl hne | (simp [instrStackPure] at hp)

theorem ofEval_wE (o : Option (Store H × Frame × Flow)) (rest : List Val) :
    (ofEval (o.map (wE rest)) : M (CallSig H) H Res) =
      ofEval o >>= fun r => pure ⟨(r.down.1, wFl rest r.down.2)⟩ := by
  rcases o with _ | ⟨s', f', fl⟩
  · exact (stuck_bind' _).symm
  · cases fl <;> simp [ofEval, wE, wFl]
    rw [map_eq_bind_pure_comp, Silmaril.Wasm.Abstract.Body.trap_bind]

theorem flatK_whisk {i : Instr} {f : Frame} {stk : List Val} {o : Option Nat}
    {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
    {labels : List Nat} (hp : instrStackPure i = true)
    (hc : flatChkE ext F mi nl ret labels stk.length i = some o) (rest : List Val) :
    (liftP (flatK i f (stk ++ rest)) : M (CallSig H) H ResP) =
      liftP (flatK i f stk) >>= fun r => pure (wP rest r) := by
  simp only [liftP, flatK, bind_assoc]
  congr 1
  funext s
  rw [evalFlat_whisk hp hc rest, ofEval_wE, bind_assoc]
  congr 1
  funext r
  simp only [pure_bind]
  rfl

theorem flatK_lands {i : Instr} {f : Frame} {stk : List Val} {o : Option Nat} {env : Env}
    {F : List (FuncInst H)} {ext : ExtArity H} (hp : instrStackPure i = true)
    (hc : flatChkE ext F env.mi env.nl env.ret env.labels stk.length i = some o)
    (hf : f.module = env.mi) :
    Lands (GoodR env o) (liftP (flatK i f stk) : M (CallSig H) H ResP) := by
  simp only [liftP, flatK, bind_assoc]
  refine lands_bind (lands_true _) fun s _ => ?_
  cases he : evalFlat s.down f stk i with
  | none => rw [ofEval, stuck_bind']; exact lands_stuck
  | some t =>
    obtain ⟨s', f', fl⟩ := t
    have hg : FlGood env.labels env.ret o fl := evalFlat_flGood hp hc he
    have hm : f'.module = env.mi := (evalFlat_module' he).trans hf
    cases fl with
    | trap => simp only [ofEval, Silmaril.Wasm.Abstract.Body.trap_bind]; exact lands_trap
    | normal vs =>
      simp only [ofEval, bind_assoc, pure_bind]
      exact lands_bind (lands_true _) fun _ _ => lands_pure ⟨hm, hg⟩
    | brk l vs =>
      simp only [ofEval, bind_assoc, pure_bind]
      exact lands_bind (lands_true _) fun _ _ => lands_pure ⟨hm, hg⟩
    | ret vs =>
      simp only [ofEval, bind_assoc, pure_bind]
      exact lands_bind (lands_true _) fun _ _ => lands_pure ⟨hm, hg⟩
    | throw a =>
      simp only [ofEval, bind_assoc, pure_bind]
      exact lands_bind (lands_true _) fun _ _ => lands_pure trivial

theorem throwRefEv_cases (f : Frame) (stk : List Val) :
    (throwRefEv (H := H) f stk = trap ⟨⟩ ∨ (∃ a, throwRefEv (H := H) f stk = pure ⟨(f, .throw a)⟩) ∨
      throwRefEv (H := H) f stk = stuck) := by
  rcases stk with _ | ⟨v, stk⟩
  · exact .inr (.inr rfl)
  · rcases v with _ | _ | r
    · exact .inr (.inr rfl)
    · exact .inr (.inr rfl)
    · cases r <;> first | exact .inl rfl | exact .inr (.inl ⟨_, rfl⟩) | exact .inr (.inr rfl)

theorem throwRefEv_append (f : Frame) (v : Val) (stk rest : List Val) :
    throwRefEv (H := H) f (v :: stk ++ rest) = throwRefEv f (v :: stk) := by
  rcases v with _ | _ | r
  · rfl
  · rfl
  · cases r <;> rfl

theorem throwRef_lands {f : Frame} {stk : List Val} {P : ResP → Prop}
    (hP : ∀ f a, P ⟨(f, .flow (.throw a))⟩) :
    Lands P (opCXP (H := H) .throwRef f stk) := by
  show Lands P (liftP (throwRefEv f stk))
  rcases throwRefEv_cases (H := H) f stk with h | ⟨a, h⟩ | h <;> rw [h, liftP]
  · rw [Silmaril.Wasm.Abstract.Body.trap_bind]; exact lands_trap
  · rw [pure_bind]; exact lands_pure (hP _ _)
  · rw [stuck_bind']; exact lands_stuck

/-- **A checked stack-pure operator is stack-polymorphic** (read through `trimP`), and its
results satisfy `GoodR`. -/
theorem op_whisk {i : Instr} {f : Frame} {stk : List Val} {o : Option Nat} {env : Env}
    {tags : List TagInst} {F : List (FuncInst H)} (hp : instrStackPure i = true)
    (hc : flatChkE (ehExt tags) F env.mi env.nl env.ret env.labels stk.length i = some o)
    (hf : f.module = env.mi) (rest : List Val) :
    Lands (GoodR env o) (opCXP (H := H) i f stk) ∧
      obsP env.labels env.ret (opCXP (H := H) i f (stk ++ rest)) =
        opCXP i f stk >>= fun r => pure (trimP env.labels env.ret (whiskP rest r)) := by
  by_cases hne : i = .throwRef
  · subst hne
    have hle : 1 ≤ stk.length := by
      simp only [flatChkE, ehExt, extStep] at hc
      by_contra hn
      simp [hn] at hc
    obtain ⟨v, stk₀, rfl⟩ : ∃ v stk₀, stk = v :: stk₀ := by
      cases stk with
      | nil => simp at hle
      | cons v stk₀ => exact ⟨v, stk₀, rfl⟩
    refine ⟨throwRef_lands fun _ _ => trivial, ?_⟩
    show obsP env.labels env.ret (liftP (throwRefEv f (v :: stk₀ ++ rest))) = _
    rw [throwRefEv_append]
    show _ = liftP (throwRefEv f (v :: stk₀)) >>= _
    rcases throwRefEv_cases (H := H) f (v :: stk₀) with h | ⟨a, h⟩ | h <;>
      simp only [h, liftP, obsP, Silmaril.Wasm.Abstract.Body.trap_bind, stuck_bind', pure_bind]
    rfl
  · have hl := flatK_lands (H := H) (f := f) hp hc hf
    rw [opCXP_flat hp hne, opCXP_flat hp hne]
    refine ⟨hl, ?_⟩
    rw [obsP, flatK_whisk hp hc rest, bind_assoc]
    refine bind_congr_lands hl fun r hr => ?_
    rw [pure_bind, trim_wP rest hr]

end Silmaril.Proofs.Wasm.Abstract.ExposePStruct
