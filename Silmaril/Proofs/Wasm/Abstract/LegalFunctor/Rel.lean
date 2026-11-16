module

public import Silmaril.Wasm.Abstract.LegalFunctor.Defs
public import Silmaril.Wasm.Abstract.WorldFunctor.Thms
public import Silmaril.Wasm.Abstract.TypedCatFit.Thms
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux
public import Silmaril.Wasm.Validation.Instructions.Properties

/-!
Proofs for `Silmaril.Wasm.Abstract.LegalFunctor.Thms`: under every legal oracle, typed code keeps
the world, composes and whiskers as under the closure (#579's proofs with
`TypedCatFit.evalOXP_goodO_fit` and `evalOXP_tensor_fit` for the closure's instances); the
restricted, trap-forgetting relations are equal exactly when the runs agree (`OpEquivL`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.LegalFunctor

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp (chkE ehExt)
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposePTyped Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.TypedFunctor Silmaril.Wasm.Abstract.WorldFunctor
open Silmaril.Wasm.Abstract.LegalFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)

variable {H : Type} {Γ : Ctx H} {C : Abstract.CallRel H}

/-! ## Legal oracles -/

theorem legal_of_arityResp (h : ArityResp Γ C) : Legal Γ C :=
  fun s s₂ a args fl hc hg => h s s₂ a args fl hc.1 hg

/-! ## Relations -/

theorem trapR_ne {g : ORel H} {s : Store H} {f : Frame} {stk : List Val} {s' : Store H}
    {f' : Frame} {o : POut} (ho : o ≠ .flow .trap) :
    trapR g s f stk s' f' o ↔ g s f stk s' f' o := by
  rcases o with (_ | _ | _ | _ | _) | _ <;> first | exact Iff.rfl | exact absurd rfl ho

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

/-- **Restricted trap-forgetting relations are equal exactly when they agree pointwise**: the
same non-trap results, and a trap for one exactly when for the other. -/
theorem resR_trapR_eq_iff (P : Store H → Frame → List Val → Prop) (g g' : ORel H) :
    resR P (trapR g) = resR P (trapR g') ↔ ∀ s f stk, P s f stk →
      (∀ s' f' (o : POut), o ≠ .flow .trap → (g s f stk s' f' o ↔ g' s f stk s' f' o)) ∧
      ((∃ s' f', g s f stk s' f' (.flow .trap)) ↔ ∃ s' f', g' s f stk s' f' (.flow .trap)) := by
  constructor
  · intro h s f stk hp
    have e : ∀ s' f' o, resR P (trapR g) s f stk s' f' o ↔ resR P (trapR g') s f stk s' f' o :=
      fun s' f' o => by rw [h]
    refine ⟨fun s' f' o ho => ?_, ?_⟩
    · have e' := e s' f' o
      unfold resR at e'
      rw [trapR_ne ho, trapR_ne ho] at e'
      exact ⟨fun h₁ => (e'.1 ⟨hp, h₁⟩).2, fun h₁ => (e'.2 ⟨hp, h₁⟩).2⟩
    · exact ⟨fun h₁ => ((e s f (.flow .trap)).1 ⟨hp, h₁⟩).2,
        fun h₁ => ((e s f (.flow .trap)).2 ⟨hp, h₁⟩).2⟩
  · intro h
    funext s f stk s' f' o
    apply propext
    by_cases hp : P s f stk
    · by_cases ho : o = .flow .trap
      · subst ho
        exact ⟨fun h₁ => ⟨hp, (h s f stk hp).2.1 h₁.2⟩, fun h₁ => ⟨hp, (h s f stk hp).2.2 h₁.2⟩⟩
      · unfold resR
        rw [trapR_ne ho, trapR_ne ho]
        exact and_congr_right fun _ => (h s f stk hp).1 s' f' o ho
    · exact ⟨fun h₁ => absurd h₁.1 hp, fun h₁ => absurd h₁.1 hp⟩

/-! ## The equivalence -/

theorem opEquivL_refl (I : TIface) (es : List BExpr) : OpEquivL Γ I es es :=
  fun _ _ _ _ _ _ => ⟨fun _ _ _ _ => Iff.rfl, Iff.rfl⟩

theorem opEquivL_symm {I : TIface} {es es' : List BExpr} (h : OpEquivL Γ I es es') :
    OpEquivL Γ I es' es :=
  fun C hC s f stk hw => ⟨fun s' f' o ho => ((h C hC s f stk hw).1 s' f' o ho).symm,
    (h C hC s f stk hw).2.symm⟩

theorem opEquivL_trans {I : TIface} {es₁ es₂ es₃ : List BExpr} (h₁ : OpEquivL Γ I es₁ es₂)
    (h₂ : OpEquivL Γ I es₂ es₃) : OpEquivL Γ I es₁ es₃ :=
  fun C hC s f stk hw => ⟨fun s' f' o ho =>
    ((h₁ C hC s f stk hw).1 s' f' o ho).trans ((h₂ C hC s f stk hw).1 s' f' o ho),
    (h₁ C hC s f stk hw).2.trans (h₂ C hC s f stk hw).2⟩

/-- **The relations of two codes agree under every legal oracle exactly when the codes are
`OpEquivL`.** -/
theorem ans_eq_iff {I : TIface} {es es' : List BExpr} :
    (∀ C, Legal Γ C → resR (WSt Γ I) (Ans C (denK es)) = resR (WSt Γ I) (Ans C (denK es'))) ↔
      OpEquivL Γ I es es' := by
  simp only [ans_denK]
  exact forall_congr' fun C => forall_congr' fun _ => resR_trapR_eq_iff _ _ _

/-- `OpEquivP` (all oracles, all states) implies `OpEquivL`. -/
theorem opEquivL_of_opEquivP {es es' : List BExpr} (h : Abstract.FunctorP.OpEquivP H es es')
    (I : TIface) : OpEquivL Γ I es es' :=
  ans_eq_iff.1 fun _ _ => by rw [(denK_eq_iff es es').2 h]

/-! ## World states under a legal oracle -/

theorem wst_chk {I : TIface} {o : Option Nat} {es : List BExpr} (hm : Mor Γ I.forget o es)
    {s : Store H} {f : Frame} {stk : List Val} (hw : WSt Γ I s f stk) :
    chkE (ehExt Γ.tags) s.funcs f.module f.locals.length I.env.ret I.env.labels
      (some stk.length) es = some o := by
  obtain ⟨hg, hf, hn, hs⟩ := hw
  rw [hg.1, hf, hn, hs]; exact hm

theorem tmor_env {I J : TIface} {ft : Bool} {es : List BExpr} (hm : TMor Γ I J ft es) :
    J.mi = I.mi ∧ J.C.locals.length = I.C.locals.length ∧ J.env = I.env := by
  obtain ⟨hmi, xs, -, hC, -, -⟩ := hm
  refine ⟨hmi, by rw [hC, Context.initLocals_locals_length], ?_⟩
  simp only [TIface.env, hmi, hC, Context.initLocals_labels, Context.initLocals_return,
    Context.initLocals_locals_length]

/-- **Typed code keeps the world under every legal oracle.** -/
theorem thom_lands_legal (hC : Legal Γ C) {I J : TIface} {es : List BExpr} (hm : THom Γ I J es)
    {s : Store H} {f : Frame} {stk : List Val} (hw : WSt Γ I s f stk) {s' : Store H}
    {f' : Frame} {vs : List Val} (d : EvalOXP C s f stk es (s', f', .flow (.normal vs))) :
    WSt Γ J s' f' vs := by
  obtain ⟨hmi, hloc, -⟩ := tmor_env hm
  obtain ⟨-, -, -, -, -, hc⟩ := hm
  obtain ⟨hg', hmod, hl, hgo⟩ := Abstract.TypedCatFit.evalOXP_goodO_fit hC d hw.1 (wst_chk hc hw)
  refine ⟨hg', by rw [hmod, hw.2.1, hmi], by rw [hl, hw.2.2.1, hloc], ?_⟩
  exact (Option.some.inj hgo).symm

theorem ans_lands_legal (hC : Legal Γ C) {I J : TIface} {es : List BExpr} (hm : THom Γ I J es) :
    ∀ s f stk s' f' vs, resR (WSt Γ I) (Ans C (denK es)) s f stk s' f'
      (.flow (.normal vs)) → WSt Γ J s' f' vs := by
  intro s f stk s' f' vs ⟨hw, h⟩
  rw [ans_denK] at h
  exact thom_lands_legal hC hm hw h

theorem ans_nil (C : Abstract.CallRel H) (I : TIface) :
    resR (WSt Γ I) (Ans C (denK (H := H) [])) = resR (WSt Γ I) idR := by
  rw [ans_denK, denR_nil, trapR_idR]

theorem ans_append_legal (hC : Legal Γ C) {I J : TIface} {es₁ : List BExpr} (h₁ : THom Γ I J es₁)
    (es₂ : List BExpr) :
    resR (WSt Γ I) (Ans C (denK (es₁ ++ es₂))) =
      seqR (resR (WSt Γ I) (Ans C (denK es₁))) (resR (WSt Γ J) (Ans C (denK es₂))) := by
  rw [seqR_resR_of_lands _ (ans_lands_legal hC h₁), ans_denK, ans_denK, ans_denK, denR_append,
    trapR_seqR, resR_seqR]

/-! ## The stack tensor under a legal oracle -/

theorem trimO_eq_trap {labels : List Nat} {ret : Nat} {o : POut} :
    trimO labels ret o = .flow .trap ↔ o = .flow .trap := by
  rcases o with (_ | _ | _ | _ | _) | _ <;> simp [trimO]

theorem whiskO_eq_trap {rest : List Val} {o : POut} :
    whiskO rest o = .flow .trap ↔ o = .flow .trap := by
  rcases o with (_ | _ | _ | _ | _) | _ <;> simp [whiskO]

theorem wst_withBelow {I : TIface} {R : List CValType} {s : Store H} {f : Frame}
    {stk' : List Val} (hw : WSt Γ (I.withBelow R) s f stk') :
    I.ts.length ≤ stk'.length ∧ WSt Γ I s f (stk'.take I.ts.length) := by
  have hlen : stk'.length = R.length + I.ts.length := by
    simpa [TIface.withBelow] using hw.2.2.2
  exact ⟨by omega, ⟨hw.1, hw.2.1, hw.2.2.1, by simp; omega⟩⟩

/-- **The answered stack tensor on world states, under every legal oracle** (#579's
`thom_whisker`, with `TypedCatFit.evalOXP_tensor_fit` in place of the closure's instance). -/
theorem thom_whisker_legal (hC : Legal Γ C) {I J : TIface} {es : List BExpr} (hm : THom Γ I J es)
    (R : List CValType) :
    trimR I.env.labels I.env.ret (resR (WSt Γ (I.withBelow R)) (trapR (denR C es))) =
      trimR I.env.labels I.env.ret (resR (WSt Γ (I.withBelow R))
        (leftR I.ts.length (resR (WSt Γ I) (trapR (denR C es))))) := by
  obtain ⟨-, -, -, -, -, hc⟩ := hm
  funext s f stk' s' f' X
  apply propext
  by_cases hw : WSt Γ (I.withBelow R) s f stk'
  swap
  · exact ⟨fun ⟨_, ⟨h, _⟩, _⟩ => absurd h hw, fun ⟨_, ⟨h, _⟩, _⟩ => absurd h hw⟩
  obtain ⟨hn, hwI⟩ := wst_withBelow hw
  have T := fun s' f' X => Abstract.TypedCatFit.evalOXP_tensor_fit hC hw.1 (wst_chk hc hwI)
    (stk'.drop I.ts.length) s' f' X
  simp only [List.take_append_drop] at T
  by_cases hX : X = .flow .trap
  · subst hX
    constructor
    · rintro ⟨o', ⟨-, h⟩, ht⟩
      rw [trimO_eq_trap] at ht; subst ht
      obtain ⟨s'', f'', h⟩ := h
      obtain ⟨o, ho, ht'⟩ := (T s'' f'' (.flow .trap)).1 ⟨_, h, rfl⟩
      rw [trimO_eq_trap, whiskO_eq_trap] at ht'; subst ht'
      exact ⟨.flow .trap, ⟨hw, hn, .flow .trap, ⟨hwI, s'', f'', ho⟩, rfl⟩, rfl⟩
    · rintro ⟨o', ⟨-, -, o, ⟨-, h⟩, rfl⟩, ht⟩
      rw [trimO_eq_trap, whiskO_eq_trap] at ht; subst ht
      obtain ⟨s'', f'', h⟩ := h
      obtain ⟨o', ho', ht'⟩ := (T s'' f'' (.flow .trap)).2 ⟨_, h, rfl⟩
      rw [trimO_eq_trap] at ht'; subst ht'
      exact ⟨.flow .trap, ⟨hw, s'', f'', ho'⟩, rfl⟩
  · constructor
    · rintro ⟨o', ⟨-, h⟩, ht⟩
      have ho' : o' ≠ .flow .trap := by rintro rfl; exact hX ht.symm
      rw [trapR_ne ho'] at h
      obtain ⟨o, ho, ht'⟩ := (T s' f' X).1 ⟨o', h, ht⟩
      have hot : o ≠ .flow .trap := by rintro rfl; exact hX ht'.symm
      exact ⟨_, ⟨hw, hn, o, ⟨hwI, (trapR_ne hot).2 ho⟩, rfl⟩, ht'⟩
    · rintro ⟨o', ⟨-, -, o, ⟨-, h⟩, rfl⟩, ht⟩
      have hot : o ≠ .flow .trap := by rintro rfl; exact hX ht.symm
      rw [trapR_ne hot] at h
      obtain ⟨o', ho', ht'⟩ := (T s' f' X).2 ⟨o, h, ht⟩
      have ho't : o' ≠ .flow .trap := by rintro rfl; exact hX ht'.symm
      exact ⟨o', ⟨hw, (trapR_ne ho't).2 ho'⟩, ht'⟩

/-- **The whiskering equation of checked code under every legal oracle**, at a state of the
checked height in a frame of the checked instance and local count, from a store agreeing with
the world. -/
theorem mor_whisker_legal (hC : Legal Γ C) {I : Iface} {oc : Option Nat} {es : List BExpr}
    (hm : Mor Γ I oc es) {s : Store H} {f : Frame} {stk : List Val} (hg : Γ.Good s)
    (hf : f.module = I.env.mi) (hn : f.locals.length = I.env.nl) (hs : stk.length = I.h)
    (rest : List Val) :
    trimR I.env.labels I.env.ret (denR C es) s f (stk ++ rest) =
      trimR I.env.labels I.env.ret (whiskR rest (denR C es)) s f (stk ++ rest) := by
  have hc : chkE (ehExt Γ.tags) s.funcs f.module f.locals.length I.env.ret I.env.labels
      (some stk.length) es = some oc := by
    rw [hg.1, hf, hn, hs]; exact hm
  funext s' f' X
  refine propext ((Abstract.TypedCatFit.evalOXP_tensor_fit hC hg hc rest s' f' X).trans ⟨?_, ?_⟩)
  · rintro ⟨o, h, rfl⟩
    exact ⟨_, ⟨stk, o, rfl, h, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨stk₀, o, he, h, rfl⟩, rfl⟩
    obtain rfl := List.append_cancel_right he
    exact ⟨o, h, rfl⟩

/-! ## Pure code -/

theorem pureAt_trapR {n n' : Nat} {φ : List Val → List Val} {g : ORel H} (hp : PureAt n n' φ g) :
    PureAt n n' φ (trapR g) := by
  refine ⟨hp.1, fun s f stk s' f' o hl => ?_⟩
  by_cases ho : o = .flow .trap
  · subst ho
    constructor
    · rintro ⟨s'', f'', h⟩
      obtain ⟨-, -, h⟩ := (hp.2 s f stk s'' f'' _ hl).1 h
      cases h
    · rintro ⟨-, -, h⟩; cases h
  · rw [trapR_ne ho]; exact hp.2 s f stk s' f' o hl

end Silmaril.Proofs.Wasm.Abstract.LegalFunctor
