module

public import Silmaril.Proofs.Wasm.Abstract.WorldFunctor.Rel
public import Silmaril.Wasm.Abstract.TypedCatFit.Thms
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping
public import Silmaril.Wasm.Execution.Core.Soundness.ProgressAux
public import Silmaril.Wasm.Validation.Instructions.Properties

/-!
Proofs for `Silmaril.Wasm.Abstract.WorldFunctor.Thms`: world states, the checker's invariant
along typed code under the closure, the codomain's composition, and the stack tensor.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.WorldFunctor

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp (chkE ehExt)
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Abstract.ExposePTyped Silmaril.Wasm.Abstract.TypedCat
open Silmaril.Wasm.Abstract.TypedFunctor Silmaril.Wasm.Abstract.WorldFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)
open Silmaril.Wasm.Abstract.XRecursionP (closedCallXP)

variable {H : Type} {Γ : Ctx H}

/-! ## World states -/

theorem realizes_wst {I : TIface} {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) : WSt Γ I s f stk := by
  obtain ⟨hg, -, hfm, ⟨C₀, hF, hIC⟩, -, -, hstk⟩ := hr
  obtain ⟨C', lts, hm, hl, rfl⟩ := hF
  refine ⟨hg, hfm, ?_, by simpa using hstk.length_eq⟩
  cases hm with
  | mk htypes => rw [hIC]; simp [hl.length_eq]

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

/-- **Typed code keeps the world**: a fallthrough of typed code `I ⟶ J` under the closure from a
world state of `I` is a world state of `J`. -/
theorem thom_lands {I J : TIface} {es : List BExpr} (hm : THom Γ I J es) {s : Store H}
    {f : Frame} {stk : List Val} (hw : WSt Γ I s f stk) {s' : Store H} {f' : Frame}
    {vs : List Val} (d : EvalOXP closedCallXP s f stk es (s', f', .flow (.normal vs))) :
    WSt Γ J s' f' vs := by
  obtain ⟨hmi, hloc, -⟩ := tmor_env hm
  obtain ⟨-, -, -, -, -, hc⟩ := hm
  obtain ⟨hg', hmod, hl, hgo⟩ := Abstract.TypedCatFit.evalOXP_goodO_closed d hw.1 (wst_chk hc hw)
  refine ⟨hg', by rw [hmod, hw.2.1, hmi], by rw [hl, hw.2.2.1, hloc], ?_⟩
  exact (Option.some.inj hgo).symm

/-! ## The world functor's relation -/

theorem gRel_supp {I : TIface} {k : Cfg → PX H Cfg} :
    ∀ s f stk s' f' o, resR (WSt Γ I) (Ans closedCallXP k) s f stk s' f' o → WSt Γ I s f stk :=
  fun _ _ _ _ _ _ h => h.1

theorem gRel_lands {I J : TIface} {es : List BExpr} (hm : THom Γ I J es) :
    ∀ s f stk s' f' vs, resR (WSt Γ I) (Ans closedCallXP (denK es)) s f stk s' f'
      (.flow (.normal vs)) → WSt Γ J s' f' vs := by
  intro s f stk s' f' vs ⟨hw, h⟩
  rw [ans_denK] at h
  exact thom_lands hm hw h

theorem gRel_trap {I : TIface} {k : Cfg → PX H Cfg} :
    ∀ s f stk s' f' s'' f'', resR (WSt Γ I) (Ans closedCallXP k) s f stk s' f' (.flow .trap) →
      resR (WSt Γ I) (Ans closedCallXP k) s f stk s'' f'' (.flow .trap) :=
  fun _ _ _ _ _ _ _ h => h

theorem gRel_eq {I : TIface} (es : List BExpr) :
    resR (WSt Γ I) (Ans closedCallXP (denK es)) = resR (WSt Γ I) (trapR (denR closedCallXP es)) := by
  rw [ans_denK]

theorem gRel_nil (I : TIface) :
    resR (WSt Γ I) (Ans closedCallXP (denK (H := H) [])) = resR (WSt Γ I) idR := by
  rw [ans_denK, denR_nil, trapR_idR]

theorem gRel_append {I J : TIface} {es₁ : List BExpr} (h₁ : THom Γ I J es₁) (es₂ : List BExpr) :
    resR (WSt Γ I) (Ans closedCallXP (denK (es₁ ++ es₂))) =
      seqR (resR (WSt Γ I) (Ans closedCallXP (denK es₁)))
        (resR (WSt Γ J) (Ans closedCallXP (denK es₂))) := by
  rw [seqR_resR_of_lands _ (gRel_lands h₁), ans_denK, ans_denK, ans_denK, denR_append,
    trapR_seqR, resR_seqR]

theorem gRel_loop (I : TIface) (bt : BlockType) (body : List BExpr) :
    resR (WSt Γ I) (Ans closedCallXP (denK [.loop bt body])) =
      resR (WSt Γ I) (trapR (iterR (loopStepR closedCallXP bt body))) := by
  rw [ans_denK, denR_loop]

theorem gRel_realizes {I : TIface} (es : List BExpr) {s : Store H} {f : Frame} {stk : List Val}
    (hr : Realizes Γ I s f stk) (s' : Store H) (f' : Frame) (o : POut) :
    resR (WSt Γ I) (Ans closedCallXP (denK es)) s f stk s' f' o ↔
      trapR (denR closedCallXP es) s f stk s' f' o := by
  rw [ans_denK]
  exact ⟨fun h => h.2, fun h => ⟨realizes_wst hr, h⟩⟩

/-! ## The codomain's identity and composition -/

theorem idR_lands {I : TIface} :
    ∀ s f stk s' f' vs, resR (WSt Γ I) idR s f stk s' f' (.flow (.normal vs)) →
      WSt Γ I s' f' vs := by
  rintro s f stk s' f' vs ⟨hw, rfl, rfl, h⟩
  cases h; exact hw

theorem idR_trap {I : TIface} :
    ∀ s f stk s' f' s'' f'', resR (WSt Γ I) (idR : ORel H) s f stk s' f' (.flow .trap) →
      resR (WSt Γ I) idR s f stk s'' f'' (.flow .trap) := by
  rintro s f stk s' f' s'' f'' ⟨-, -, -, h⟩
  cases h

theorem seqR_supp {P : Store H → Frame → List Val → Prop} {g₁ : ORel H} (g₂ : ORel H)
    (h₁ : ∀ s f stk s' f' o, g₁ s f stk s' f' o → P s f stk) :
    ∀ s f stk s' f' o, seqR g₁ g₂ s f stk s' f' o → P s f stk := by
  rintro s f stk s' f' o (⟨_, _, _, h, -⟩ | ⟨h, -⟩) <;> exact h₁ _ _ _ _ _ _ h

theorem seqR_lands {Q : Store H → Frame → List Val → Prop} (g₁ : ORel H) {g₂ : ORel H}
    (h₂ : ∀ s f stk s' f' vs, g₂ s f stk s' f' (.flow (.normal vs)) → Q s' f' vs) :
    ∀ s f stk s' f' vs, seqR g₁ g₂ s f stk s' f' (.flow (.normal vs)) → Q s' f' vs := by
  rintro s f stk s' f' vs (⟨_, _, _, -, h⟩ | ⟨-, hn⟩)
  · exact h₂ _ _ _ _ _ _ h
  · exact absurd trivial hn

theorem seqR_trap {g₁ g₂ : ORel H}
    (h₁ : ∀ s f stk s' f' s'' f'', g₁ s f stk s' f' (.flow .trap) → g₁ s f stk s'' f'' (.flow .trap))
    (h₂ : ∀ s f stk s' f' s'' f'', g₂ s f stk s' f' (.flow .trap) → g₂ s f stk s'' f'' (.flow .trap)) :
    ∀ s f stk s' f' s'' f'', seqR g₁ g₂ s f stk s' f' (.flow .trap) →
      seqR g₁ g₂ s f stk s'' f'' (.flow .trap) := by
  rintro s f stk s' f' s'' f'' (⟨a, b, c, h, h'⟩ | ⟨h, hn⟩)
  · exact .inl ⟨a, b, c, h, h₂ _ _ _ _ _ _ _ h'⟩
  · exact .inr ⟨h₁ _ _ _ _ _ _ _ h, hn⟩

/-! ## The stack tensor -/

theorem withBelow_ok {I : TIface} (hI : I.Ok) {R : List CValType} (hR : ResultOk {} R) :
    (I.withBelow R).Ok := by
  intro t ht
  rcases List.mem_append.1 ht with h | h
  · exact TyOk.of_empty _ (hR t h)
  · exact hI t h

theorem resultOk_of_closed {Δ : TypeCtx} {R : List CValType} (hR : ResultOk {} R) :
    ResultOk Δ R := fun t ht => TyOk.of_empty Δ (hR t ht)

theorem trimO_eq_trap {labels : List Nat} {ret : Nat} {o : POut} :
    trimO labels ret o = .flow .trap ↔ o = .flow .trap := by
  rcases o with (_ | _ | _ | _ | _) | _ <;> simp [trimO]

theorem whiskO_eq_trap {rest : List Val} {o : POut} :
    whiskO rest o = .flow .trap ↔ o = .flow .trap := by
  rcases o with (_ | _ | _ | _ | _) | _ <;> simp [whiskO]

theorem whiskO_eq_normal {rest vs : List Val} {o : POut} (h : whiskO rest o = .flow (.normal vs)) :
    ∃ us, o = .flow (.normal us) ∧ vs = us ++ rest := by
  rcases o with (us | _ | _ | _ | _) | _ <;> simp [whiskO] at h
  exact ⟨us, rfl, h.symm⟩

theorem wst_withBelow {I : TIface} {R : List CValType} {s : Store H} {f : Frame}
    {stk' : List Val} (hw : WSt Γ (I.withBelow R) s f stk') :
    I.ts.length ≤ stk'.length ∧ WSt Γ I s f (stk'.take I.ts.length) ∧
      (stk'.drop I.ts.length).length = R.length := by
  have hlen : stk'.length = R.length + I.ts.length := by
    simpa [TIface.withBelow] using hw.2.2.2
  refine ⟨by omega, ⟨hw.1, hw.2.1, hw.2.2.1, by simp; omega⟩, by simp; omega⟩

/-- **The answered stack tensor on world states**: for typed code `I ⟶ J` under the closure, at
the world states of `I` with `R` below, the runs read at the targets' arities are the whiskered
runs at the world states of `I`. -/
theorem thom_whisker {I J : TIface} {es : List BExpr} (hm : THom Γ I J es) (R : List CValType) :
    trimR I.env.labels I.env.ret (resR (WSt Γ (I.withBelow R)) (trapR (denR closedCallXP es))) =
      trimR I.env.labels I.env.ret (resR (WSt Γ (I.withBelow R))
        (leftR I.ts.length (resR (WSt Γ I) (trapR (denR closedCallXP es))))) := by
  obtain ⟨-, -, -, -, -, hc⟩ := hm
  funext s f stk' s' f' X
  apply propext
  by_cases hw : WSt Γ (I.withBelow R) s f stk'
  swap
  · exact ⟨fun ⟨_, ⟨h, _⟩, _⟩ => absurd h hw, fun ⟨_, ⟨h, _⟩, _⟩ => absurd h hw⟩
  obtain ⟨hn, hwI, -⟩ := wst_withBelow hw
  have T := fun s' f' X => Abstract.TypedCatFit.evalOXP_tensor_closed hw.1 (wst_chk hc hwI)
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

/-! ## The codomain's whiskering -/

theorem whisk_supp {I : TIface} (R : List CValType) (n : Nat) (g : ORel H) :
    ∀ s f stk s' f' o, resR (WSt Γ (I.withBelow R)) (leftR n g) s f stk s' f' o →
      WSt Γ (I.withBelow R) s f stk :=
  fun _ _ _ _ _ _ h => h.1

theorem whisk_lands {I J : TIface} (R : List CValType) {g : ORel H}
    (hl : ∀ s f stk s' f' vs, g s f stk s' f' (.flow (.normal vs)) → WSt Γ J s' f' vs) :
    ∀ s f stk s' f' vs, resR (WSt Γ (I.withBelow R)) (leftR I.ts.length g) s f stk s' f'
      (.flow (.normal vs)) → WSt Γ (J.withBelow R) s' f' vs := by
  rintro s f stk s' f' vs ⟨hw, -, o, h, ho⟩
  obtain ⟨us, rfl, rfl⟩ := whiskO_eq_normal ho.symm
  obtain ⟨-, -, hd⟩ := wst_withBelow hw
  obtain ⟨hg, hmod, hloc, hlen⟩ := hl _ _ _ _ _ _ h
  refine ⟨hg, hmod, hloc, ?_⟩
  simp only [TIface.withBelow, List.length_append, hlen, hd]
  omega

theorem whisk_trap {I : TIface} (R : List CValType) (n : Nat) {g : ORel H}
    (ht : ∀ s f stk s' f' s'' f'', g s f stk s' f' (.flow .trap) → g s f stk s'' f'' (.flow .trap)) :
    ∀ s f stk s' f' s'' f'', resR (WSt Γ (I.withBelow R)) (leftR n g) s f stk s' f' (.flow .trap) →
      resR (WSt Γ (I.withBelow R)) (leftR n g) s f stk s'' f'' (.flow .trap) := by
  rintro s f stk s' f' s'' f'' ⟨hw, hn, o, h, ho⟩
  have hot : o = .flow .trap := whiskO_eq_trap.1 ho.symm
  subst hot
  exact ⟨hw, hn, _, ht _ _ _ _ _ _ _ h, ho⟩

/-! ## Pure code -/

theorem pureAt_trapR {n n' : Nat} {φ : List Val → List Val} {g : ORel H} (hp : PureAt n n' φ g) :
    PureAt n n' φ (trapR g) := by
  refine ⟨hp.1, fun s f stk s' f' o hl => ?_⟩
  by_cases ho : o = .flow .trap
  · subst ho
    rw [trapR_trap]
    constructor
    · rintro ⟨s'', f'', h⟩
      obtain ⟨-, -, h⟩ := (hp.2 s f stk s'' f'' _ hl).1 h
      cases h
    · rintro ⟨-, -, h⟩; cases h
  · rw [trapR_ne ho]; exact hp.2 s f stk s' f' o hl

end Silmaril.Proofs.Wasm.Abstract.WorldFunctor
