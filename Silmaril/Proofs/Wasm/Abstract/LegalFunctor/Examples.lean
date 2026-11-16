module

public import Silmaril.Proofs.Wasm.Abstract.LegalFunctor.Rel
public import Silmaril.Wasm.Validation.Check.TyOk

/-!
Proofs for `Silmaril.Wasm.Abstract.LegalFunctor.Thms`: the two concrete examples, restated here
because their originals live in other topics' proof modules.

* `Obs`: #572's obstruction data (`TypedFunctor` proofs, `Ex`): `call 0; drop` with a callee
  `[] → [i32]` and one passive value. Every legal oracle satisfies the whiskering equation there;
  the oracle answering with no values breaks it and is not legal.
* `Inter`: #543's interchange data (`TypedCat` proofs, `Ex`): `call 0` and `call 1` under an oracle
  with typed answers that records its callee in the store. The two orders differ in the
  restricted, trap-forgetting relations of the legal codomain.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.LegalFunctor

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.TypedCat Silmaril.Wasm.Abstract.WorldFunctor
open Silmaril.Wasm.Abstract.TypedFunctor
open Silmaril.Wasm.Abstract.LegalFunctor
open Silmaril.Wasm.Abstract.CallXP (POut EvalOXP)

/-! ## The whiskering obstruction under an illegal answer -/

namespace Obs

/-- The function type `[] → [i32]`. -/
def d₁ : DefType :=
  .defn (.group (.cons (.sub true .nil (.func .nil (.cons (.num (.int .i32)) .nil))) .nil)) 0

/-- A host function of type `[] → [i32]`. -/
def fi₁ : FuncInst Unit := ⟨d₁, {}, .host ()⟩

theorem storeChk₁ : StoreChkE (ehExt ([] : List TagInst)) [fi₁] := by
  intro a fi fn ps rs ha hc _
  rcases a with _ | a
  · simp at ha
    subst ha
    cases hc
  · simp at ha

/-- The world: no tags, one host function of type `[] → [i32]`. -/
def Γ₁ : Ctx Unit := ⟨[], [fi₁], storeChk₁⟩

def mi₁ : ModuleInst := { funcs := [0] }

/-- The interface: no locals, no labels, no results, the empty stack. -/
def I₁ : Iface := ⟨⟨mi₁, 0, 0, []⟩, 0⟩

/-- `call 0; drop`. -/
def es₁ : List BExpr := [.op (.call ⟨0⟩) [], .op .drop []]

theorem mor₁ : Mor Γ₁ I₁ (some I₁.h) es₁ := by
  show chkIn Γ₁ I₁.env (some I₁.h) es₁ = some (some 0)
  decide +kernel

def s₁ : Store Unit := { funcs := [fi₁] }

def f₁ : Frame := { module := mi₁ }

def v₁ : Val := ofInt .i32 0

theorem good₁ : Γ₁.Good s₁ := ⟨rfl, rfl, fun a e h => by simp [s₁] at h⟩

/-- The oracle of #572's obstruction: every call returns no values. -/
def C₁ : Abstract.CallRel Unit := fun s _ _ out => out = (s, .normal [])

theorem funcType₁ : DefType.funcType? fi₁.type = some ([], [.num (.int .i32)]) := rfl

/-- `C₁` is not legal: its answer to the fitting call of `[] → [i32]` has no values. -/
theorem not_legal₁ : ¬ Legal Γ₁ C₁ := by
  intro h
  have hfit : fitP C₁ s₁ 0 [] (s₁, .normal []) := by
    refine ⟨rfl, fun fi ps rs hfi hty => ?_⟩
    have hf : fi = fi₁ := by simpa [s₁] using hfi.symm
    subst hf
    rw [funcType₁] at hty
    cases hty
    rfl
  have := (h s₁ s₁ 0 [] (.normal []) hfit good₁).2 fi₁ [] [.num (.int .i32)] [] rfl funcType₁ rfl
  simp at this

theorem not_arityResp₁ : ¬ ArityResp Γ₁ C₁ := fun h => not_legal₁ (legal_of_arityResp h)

/-- With one passive value below, the answer short of the callee's result makes `drop` pop the
passive value. -/
theorem run₁ : EvalOXP C₁ s₁ f₁ [v₁] es₁ (s₁, f₁, .flow (.normal [])) :=
  .callOk (stk₁ := [v₁]) (a := 0) (fi := fi₁) (ps := []) (rs := [.num (.int .i32)]) (vs := [])
    .nil rfl rfl rfl rfl (.opOk (fun _ h => by cases h) .nil rfl .nil)

/-- **The relational whiskering equation fails under `C₁`.** -/
theorem not_whiskerR₁ :
    ¬ (trimR I₁.env.labels I₁.env.ret (denR C₁ es₁) s₁ f₁ ([] ++ [v₁]) =
      trimR I₁.env.labels I₁.env.ret (whiskR [v₁] (denR C₁ es₁)) s₁ f₁ ([] ++ [v₁])) := by
  intro h
  have h₁ : trimR I₁.env.labels I₁.env.ret (denR C₁ es₁) s₁ f₁ ([] ++ [v₁]) s₁ f₁
      (.flow (.normal [])) := ⟨_, run₁, rfl⟩
  rw [h] at h₁
  obtain ⟨_, ⟨stk₀, o, -, -, rfl⟩, ho⟩ := h₁
  rcases o with ((us | _ | _ | _ | _) | _) <;> simp [whiskO, trimO] at ho

/-- **The audit of #572's obstruction.** -/
theorem audit :
    Mor Γ₁ I₁ (some I₁.h) es₁ ∧ Γ₁.Good s₁ ∧ f₁.module = I₁.env.mi ∧
      f₁.locals.length = I₁.env.nl ∧ ([] : List Val).length = I₁.h ∧
      (∀ C, Legal Γ₁ C →
        trimR I₁.env.labels I₁.env.ret (denR C es₁) s₁ f₁ ([] ++ [v₁]) =
          trimR I₁.env.labels I₁.env.ret (whiskR [v₁] (denR C es₁)) s₁ f₁ ([] ++ [v₁])) ∧
      C₁ s₁ 0 [] (s₁, .normal []) ∧ ¬ ArityResp Γ₁ C₁ ∧ ¬ Legal Γ₁ C₁ ∧
      ¬ (trimR I₁.env.labels I₁.env.ret (denR C₁ es₁) s₁ f₁ ([] ++ [v₁]) =
        trimR I₁.env.labels I₁.env.ret (whiskR [v₁] (denR C₁ es₁)) s₁ f₁ ([] ++ [v₁])) :=
  ⟨mor₁, good₁, rfl, rfl, rfl,
    fun _ hC => mor_whisker_legal hC mor₁ good₁ rfl rfl rfl [v₁],
    rfl, not_arityResp₁, not_legal₁, not_whiskerR₁⟩

end Obs

/-! ## Interchange fails in the legal codomain -/

namespace Inter

/-- The function type `[] → []`. -/
def d₀ : DefType := .defn (.group (.cons (.sub true .nil (.func .nil .nil)) .nil)) 0

theorem he₀ : Expand d₀ (.func .nil .nil) := .mk (fin := true) (sups := .nil) rfl

theorem tyOk₀ : TyOk {} d₀ := TyOk.check_sound (by decide +kernel)

theorem funcType₀ : DefType.funcType? d₀ = some ([], []) := rfl

/-- A host function of type `[] → []`. -/
def fi₀ : FuncInst Unit := ⟨d₀, {}, .host ()⟩

theorem storeChk₀ : StoreChkE (ehExt ([] : List TagInst)) [fi₀, fi₀] := by
  intro a fi fn ps rs ha hc _
  rcases a with _ | _ | a <;> simp at ha <;> subst ha <;> cases hc

/-- The world: no tags, two host functions of type `[] → []`. -/
def Γ₀ : Ctx Unit := ⟨[], [fi₀, fi₀], storeChk₀⟩

/-- The call `a` recorded in the store. -/
def mark (s : Store Unit) (a : Nat) : Store Unit :=
  { s with elems := s.elems ++ [⟨.ref true .bot, List.replicate a .null⟩] }

/-- The oracle: a call records its callee in the store and returns no values. -/
def C₀ : Abstract.CallRel Unit := fun s a _ out => out = (mark s a, .normal [])

def mi₀ : ModuleInst := { funcs := [0, 1] }

def ctx₀ : Context := { funcs := [d₀, d₀], return_ := some [], refs := List.range 0 }

def I₀ : TIface := ⟨mi₀, ctx₀, []⟩

def s₀ : Store Unit := { funcs := [fi₀, fi₀] }

def f₀ : Frame := { module := mi₀ }

def callE (x : Fin (2 ^ 32)) : List BExpr := [.op (.call ⟨x⟩) []]

theorem typedAns₀ : TypedAns Γ₀ C₀ := by
  intro s s₂ a args fl hc hg
  simp only [C₀, Prod.mk.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  refine ⟨hg, fun fi ps rs vs hfi hty hvs => ?_⟩
  simp only [Flow.retVals, Option.some.injEq] at hvs
  subst hvs
  rw [hg.1] at hfi
  have hfi' : fi = fi₀ := by
    rcases a with _ | _ | a <;> simp [Γ₀] at hfi <;> exact hfi.symm
  subst hfi'
  have h2 : DefType.funcType? fi₀.type = some ([], []) := funcType₀
  rw [h2] at hty
  simp only [Option.some.injEq, Prod.mk.injEq] at hty
  obtain ⟨rfl, rfl⟩ := hty
  simp

theorem coh₀ : Coh Γ₀ I₀ := by
  refine ⟨rfl, fun x d hx => ?_, fun x d hx => ?_⟩
  · rcases x with _ | _ | x <;> simp [I₀, ctx₀] at hx <;> subst hx
    · exact ⟨0, fi₀, rfl, rfl, tyOk₀, .inl rfl⟩
    · exact ⟨1, fi₀, rfl, rfl, tyOk₀, .inl rfl⟩
  · simp [I₀, ctx₀] at hx

theorem ok₀ : I₀.Ok := fun t ht => by cases ht

theorem thom_callE (x : Fin (2 ^ 32)) (hx : x.val < 2) : THom Γ₀ I₀ I₀ (callE x) := by
  have hf : I₀.C.funcs[(⟨x⟩ : FuncIdx).toNat]? = some d₀ := by
    show [d₀, d₀][x.val]? = some d₀
    rcases x with ⟨_ | _ | x, h⟩
    · rfl
    · rfl
    · change x + 1 + 1 < 2 at hx
      omega
  exact Silmaril.Wasm.Abstract.TypedCat.thom_call coh₀ (ps := .nil) (rs := .nil) (pre := []) rfl
    (fun t ht => by cases ht) hf he₀

theorem good₀ : Γ₀.Good s₀ := ⟨rfl, rfl, fun a e h => by simp [s₀] at h⟩

theorem wst₀ {s : Store Unit} (hg : Γ₀.Good s) : WSt Γ₀ I₀ s f₀ [] := ⟨hg, rfl, rfl, rfl⟩

/-- Every run of a call from the empty stack records the call. -/
theorem call_inv {s : Store Unit} {x : FuncIdx} {a₀ : Nat}
    (hfx : f₀.module.funcs[x.toNat]? = some a₀) {s' : Store Unit} {f' : Frame} {o : POut}
    (h : EvalOXP C₀ s f₀ [] [.op (.call x) []] (s', f', o)) :
    s' = mark s a₀ ∧ f' = f₀ ∧ o = .flow (.normal []) := by
  cases h with
  | argsAbort hargs ho => cases hargs; exact absurd trivial ho
  | callOk hargs hfi hty hcall hvs hk =>
    cases hargs
    simp only [Store.func?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq, Prod.mk.injEq] at hfi
    obtain ⟨a', ha, fi', -, rfl, rfl⟩ := hfi
    rw [hfx] at ha
    cases ha
    simp only [C₀, Prod.mk.injEq] at hcall
    obtain ⟨rfl, rfl⟩ := hcall
    simp only [Flow.retVals, Option.some.injEq] at hvs
    subst hvs
    cases hk
    simp
  | callTrap hargs hfi hty hcall => simp [C₀] at hcall
  | callThrow hargs hfi hty hcall => simp [C₀] at hcall
  | opOk hi => exact absurd rfl (hi _)
  | opStop hi => exact absurd rfl (hi _)
  | tail _ hres => cases hres
  | tailRes _ hres => cases hres

theorem call_run {s : Store Unit} {x : FuncIdx} {a₀ : Nat}
    (hfx : f₀.module.funcs[x.toNat]? = some a₀) (hfi : s.funcs[a₀]? = some fi₀) :
    EvalOXP C₀ s f₀ [] [.op (.call x) []] (mark s a₀, f₀, .flow (.normal [])) :=
  .callOk (stk₁ := []) (a := a₀) (fi := fi₀) .nil (by simp [Store.func?, hfx, hfi]) funcType₀ rfl
    rfl .nil

/-- **The two orders differ in the legal codomain's relations.** -/
theorem not_interchange₀ :
    ¬ Interchange 0 0 (resR (WSt Γ₀ I₀) (trapR (denR C₀ (callE 0))))
      (resR (WSt Γ₀ I₀) (trapR (denR C₀ (callE 1)))) := by
  intro h
  have pos : seqR (leftR 0 (resR (WSt Γ₀ I₀) (trapR (denR C₀ (callE 0)))))
      (rightR 0 (resR (WSt Γ₀ I₀) (trapR (denR C₀ (callE 1))))) s₀ f₀ []
      (mark (mark s₀ 0) 1) f₀ (.flow (.normal [])) :=
    .inl ⟨mark s₀ 0, f₀, [], ⟨le_refl _, .flow (.normal []), ⟨wst₀ good₀, call_run rfl rfl⟩, rfl⟩,
      ⟨le_refl _, .flow (.normal []), ⟨wst₀ good₀, call_run rfl rfl⟩, rfl⟩⟩
  unfold Interchange at h
  rw [h] at pos
  rcases pos with (⟨s₁, f₁, vs, ⟨-, o₂, ⟨-, h₂⟩, hv⟩, ⟨-, o₁, ⟨-, h₁⟩, ho⟩⟩ | ⟨-, hn⟩)
  · rcases o₂ with ((us | _ | _ | _ | _) | _) <;> simp [aboveO] at hv
    subst hv
    obtain ⟨rfl, rfl, hu⟩ := call_inv (x := ⟨1⟩) (a₀ := 1) rfl h₂
    cases hu
    rcases o₁ with ((us | _ | _ | _ | _) | _) <;> simp [whiskO] at ho
    subst ho
    obtain ⟨h1, -, -⟩ := call_inv (x := ⟨0⟩) (a₀ := 0) rfl h₁
    have := congrArg Store.elems h1
    simp [mark, s₀] at this
  · exact absurd trivial hn

/-- **Interchange fails in the legal codomain**, for typed calls under a legal oracle with typed
answers (#543's `not_interchange`, restated). -/
theorem not_interchange_legal :
    ∃ (Γ : Ctx Unit) (C : Abstract.CallRel Unit) (I : TIface) (e₁ e₂ : List BExpr),
      TypedAns Γ C ∧ ArityResp Γ C ∧ I.Ok ∧ Coh Γ I ∧ THom Γ I I e₁ ∧ THom Γ I I e₂ ∧
        ¬ Interchange 0 0 (resR (WSt Γ I) (Ans C (denK e₁)))
          (resR (WSt Γ I) (Ans C (denK e₂))) := by
  refine ⟨Γ₀, C₀, I₀, callE 0, callE 1, typedAns₀, arityResp_of_typedAns typedAns₀, ok₀, coh₀,
    thom_callE 0 (by decide), thom_callE 1 (by decide), ?_⟩
  rw [ans_denK, ans_denK]
  exact not_interchange₀

end Inter

end Silmaril.Proofs.Wasm.Abstract.LegalFunctor
