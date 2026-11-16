module

public import Silmaril.Proofs.Wasm.Abstract.TypedCat.Append
public import Silmaril.Proofs.Wasm.Abstract.TypedCat.Coh

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCat.Thms`: the relations of answered runs form a category
(`idR`, `seqR`) into which the code denotes functorially (`denR_nil`, `denR_append`); the
whiskering `whiskR` is a strength: it preserves identities and composition and is associative and
unital in the passive stack. On typed code under an arity-respecting oracle, the denotation on a
stack with a passive suffix is the whiskered denotation, read at the targets' arities.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.TypedCat

variable {H : Type} {C : Abstract.CallRel H} {Γ : Ctx H}

/-! ## Body results -/

theorem whiskO_nil (o : POut) : whiskO [] o = o := by
  rcases o with (vs | _ | _ | _ | _) | _ <;> simp [whiskO]

theorem whiskO_append (R₁ R₂ : List Val) (o : POut) :
    whiskO (R₁ ++ R₂) o = whiskO R₂ (whiskO R₁ o) := by
  rcases o with (vs | _ | _ | _ | _) | _ <;> simp [whiskO]

theorem whiskO_abrupt' {rest : List Val} {o : POut} (h : ¬ o.IsNormal) : whiskO rest o = o := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    first | rfl | exact absurd trivial h

theorem whiskO_normal_inv {rest w : List Val} {o : POut}
    (h : whiskO rest o = .flow (.normal w)) : ∃ vs, o = .flow (.normal vs) ∧ w = vs ++ rest := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;> simp [whiskO] at h
  exact ⟨vs, rfl, h.symm⟩

theorem notNormal_whiskO {rest : List Val} {o : POut} (h : ¬ (whiskO rest o).IsNormal) :
    ¬ o.IsNormal := by
  intro hn
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    first | exact h trivial | exact hn

theorem isNormal_inv {o : POut} (h : o.IsNormal) : ∃ vs, o = .flow (.normal vs) := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    first | exact ⟨vs, rfl⟩ | exact absurd h id

/-! ## The category of answered runs -/

theorem seqR_idR_left (g : ORel H) : seqR idR g = g := by
  funext s f stk s' f' o
  apply propext
  constructor
  · rintro (⟨s₁, f₁, vs, ⟨rfl, rfl, h⟩, h₂⟩ | ⟨⟨rfl, rfl, rfl⟩, hn⟩)
    · simp only [POut.flow.injEq, Flow.normal.injEq] at h
      subst h; exact h₂
    · exact absurd trivial hn
  · intro hg
    exact .inl ⟨s, f, stk, ⟨rfl, rfl, rfl⟩, hg⟩

theorem seqR_idR_right (g : ORel H) : seqR g idR = g := by
  funext s f stk s' f' o
  apply propext
  constructor
  · rintro (⟨s₁, f₁, vs, h₁, ⟨rfl, rfl, rfl⟩⟩ | ⟨h₁, -⟩)
    · exact h₁
    · exact h₁
  · intro hg
    by_cases hn : o.IsNormal
    · obtain ⟨vs, rfl⟩ := isNormal_inv hn
      exact .inl ⟨s', f', vs, hg, rfl, rfl, rfl⟩
    · exact .inr ⟨hg, hn⟩

theorem seqR_assoc (g₁ g₂ g₃ : ORel H) : seqR (seqR g₁ g₂) g₃ = seqR g₁ (seqR g₂ g₃) := by
  funext s f stk s' f' o
  apply propext
  constructor
  · rintro (⟨s₂, f₂, ws, (⟨s₁, f₁, vs, h₁, h₂⟩ | ⟨h₁, hn⟩), h₃⟩ |
      ⟨(⟨s₁, f₁, vs, h₁, h₂⟩ | ⟨h₁, -⟩), hn⟩)
    · exact .inl ⟨s₁, f₁, vs, h₁, .inl ⟨s₂, f₂, ws, h₂, h₃⟩⟩
    · exact absurd trivial hn
    · exact .inl ⟨s₁, f₁, vs, h₁, .inr ⟨h₂, hn⟩⟩
    · exact .inr ⟨h₁, hn⟩
  · rintro (⟨s₁, f₁, vs, h₁, (⟨s₂, f₂, ws, h₂, h₃⟩ | ⟨h₂, hn⟩)⟩ | ⟨h₁, hn⟩)
    · exact .inl ⟨s₂, f₂, ws, .inl ⟨s₁, f₁, vs, h₁, h₂⟩, h₃⟩
    · exact .inr ⟨.inl ⟨s₁, f₁, vs, h₁, h₂⟩, hn⟩
    · exact .inr ⟨.inr ⟨h₁, hn⟩, hn⟩

/-! ## The denotation is a functor -/

theorem denR_nil : denR C [] = idR := by
  funext s f stk s' f' o
  apply propext
  constructor
  · intro h; cases h; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩; exact .nil

theorem denR_append (es₁ es₂ : List BExpr) :
    denR C (es₁ ++ es₂) = seqR (denR C es₁) (denR C es₂) := by
  funext s f stk s' f' o
  exact propext evalOXP_append_iff

/-! ## The whiskering is a strength -/

theorem whiskR_nil (g : ORel H) : whiskR [] g = g := by
  funext s f stk s' f' o
  apply propext
  constructor
  · rintro ⟨stk₀, o₀, rfl, h, rfl⟩
    rw [List.append_nil, whiskO_nil]; exact h
  · intro h
    exact ⟨stk, o, (List.append_nil stk).symm, h, (whiskO_nil o).symm⟩

theorem whiskR_append (R₁ R₂ : List Val) (g : ORel H) :
    whiskR (R₁ ++ R₂) g = whiskR R₂ (whiskR R₁ g) := by
  funext s f stk s' f' o
  apply propext
  constructor
  · rintro ⟨stk₀, o₀, rfl, h, rfl⟩
    exact ⟨stk₀ ++ R₁, whiskO R₁ o₀, by rw [List.append_assoc], ⟨stk₀, o₀, rfl, h, rfl⟩,
      whiskO_append R₁ R₂ o₀⟩
  · rintro ⟨stk₁, o₁, rfl, ⟨stk₀, o₀, rfl, h, rfl⟩, rfl⟩
    exact ⟨stk₀, o₀, by rw [List.append_assoc], h, (whiskO_append R₁ R₂ o₀).symm⟩

theorem whiskR_seqR (R : List Val) (g₁ g₂ : ORel H) :
    whiskR R (seqR g₁ g₂) = seqR (whiskR R g₁) (whiskR R g₂) := by
  funext s f stk s' f' o
  apply propext
  constructor
  · rintro ⟨stk₀, o₀, rfl, (⟨s₁, f₁, vs, h₁, h₂⟩ | ⟨h₁, hn⟩), rfl⟩
    · exact .inl ⟨s₁, f₁, vs ++ R, ⟨stk₀, _, rfl, h₁, rfl⟩, ⟨vs, o₀, rfl, h₂, rfl⟩⟩
    · refine .inr ⟨⟨stk₀, o₀, rfl, h₁, rfl⟩, ?_⟩
      rw [whiskO_abrupt' hn]; exact hn
  · rintro (⟨s₁, f₁, vs', ⟨stk₀, o₁, rfl, h₁, ho₁⟩, ⟨stk₂, o₂, hst, h₂, rfl⟩⟩ |
      ⟨⟨stk₀, o₀, rfl, h₁, rfl⟩, hn⟩)
    · obtain ⟨vs, rfl, rfl⟩ := whiskO_normal_inv ho₁.symm
      have e : stk₂ = vs := (List.append_cancel_right hst).symm
      subst e
      exact ⟨stk₀, o₂, rfl, .inl ⟨s₁, f₁, stk₂, h₁, h₂⟩, rfl⟩
    · exact ⟨stk₀, o₀, rfl, .inr ⟨h₁, notNormal_whiskO hn⟩, rfl⟩

theorem whiskR_idR (R : List Val) {s : Store H} {f : Frame} {stk' : List Val} {s' : Store H}
    {f' : Frame} {o : POut} :
    whiskR R idR s f stk' s' f' o ↔ (∃ stk, stk' = stk ++ R) ∧ idR s f stk' s' f' o := by
  constructor
  · rintro ⟨stk, o₀, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩
    exact ⟨⟨stk, rfl⟩, rfl, rfl, rfl⟩
  · rintro ⟨⟨stk, rfl⟩, rfl, rfl, rfl⟩
    exact ⟨stk, _, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩

/-! ## Typed code: the tensor as a strength -/

/-- The whiskered denotation on a stack with the passive suffix. -/
theorem whiskR_denR_iff (rest : List Val) {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {s' : Store H} {f' : Frame} {o' : POut} :
    whiskR rest (denR C es) s f (stk ++ rest) s' f' o' ↔
      ∃ o, EvalOXP C s f stk es (s', f', o) ∧ o' = whiskO rest o := by
  constructor
  · rintro ⟨stk₀, o, hst, h, rfl⟩
    rw [List.append_cancel_right hst]
    exact ⟨o, h, rfl⟩
  · rintro ⟨o, h, rfl⟩
    exact ⟨stk, o, rfl, h, rfl⟩

/-- **The answered tensor, relationally**: on typed code at a typed state, the runs on a stack
with a passive suffix are the whiskered runs, read at the targets' arities. -/
theorem tmor_tensorR (hC : ArityResp Γ C) {I J : TIface} {ft : Bool} {es : List BExpr}
    (hm : TMor Γ I J ft es) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H) (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR C es) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret (whiskR rest (denR C es)) s f (stk ++ rest) s' f' X := by
  refine (Silmaril.Wasm.Abstract.ExposePTyped.tmor_tensor hC hm hr rest s' f' X).trans ?_
  constructor
  · rintro ⟨o, h, rfl⟩
    exact ⟨_, (whiskR_denR_iff rest).2 ⟨o, h, rfl⟩, rfl⟩
  · rintro ⟨o', ho', rfl⟩
    obtain ⟨o, h, rfl⟩ := (whiskR_denR_iff rest).1 ho'
    exact ⟨o, h, rfl⟩

/-- **Whiskering preserves composition** on typed code. -/
theorem tmor_tensorR_comp (hC : ArityResp Γ C) {I J K : TIface} {ft : Bool}
    {es₁ es₂ : List BExpr} (h₁ : THom Γ I J es₁) (h₂ : TMor Γ J K ft es₂) {s : Store H}
    {f : Frame} {stk : List Val} (hr : Realizes Γ I s f stk) (rest : List Val) (s' : Store H)
    (f' : Frame) (X : POut) :
    trimR I.env.labels I.env.ret (denR C (es₁ ++ es₂)) s f (stk ++ rest) s' f' X ↔
      trimR I.env.labels I.env.ret (seqR (whiskR rest (denR C es₁)) (whiskR rest (denR C es₂)))
        s f (stk ++ rest) s' f' X := by
  rw [tmor_tensorR hC (Silmaril.Wasm.Abstract.ExposePTyped.tmor_comp h₁ h₂) hr rest s' f' X,
    denR_append, whiskR_seqR]

/-- **Whiskering preserves the identity.** -/
theorem whiskR_denR_nil (rest : List Val) (s : Store H) (f : Frame) (stk : List Val)
    (s' : Store H) (f' : Frame) (o : POut) :
    whiskR rest (denR C []) s f (stk ++ rest) s' f' o ↔ idR s f (stk ++ rest) s' f' o := by
  rw [denR_nil, whiskR_idR]
  exact ⟨fun h => h.2, fun h => ⟨⟨stk, rfl⟩, h⟩⟩

end Silmaril.Proofs.Wasm.Abstract.TypedCat
