module

public import Silmaril.Proofs.Wasm.Abstract.TypedCat.Strength
public import Silmaril.Proofs.Wasm.Abstract.TypedCat.Answer
public import Silmaril.Wasm.Validation.Check.TyOk

/-!
Proofs for `Silmaril.Wasm.Abstract.TypedCat.Thms`: **the structure is premonoidal, not
monoidal.**

* Pure morphisms are central (`interchange_of_pure`): a total, effect-free stack function on the
  top commutes with any relation below it. The identity and integer constants are pure
  (`pureAt_nil`, `pureAt_intConst`).
* The interchange law fails for calls (`not_interchange`): in a two-function store whose oracle
  records each call in the store, at a state the typed interface describes, `call 0` and `call 1`
  are typed endomorphisms of the empty stack and the oracle answers at the callees' (empty) result
  types, but the two orders of the calls reach different stores.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.TypedCat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.TypedCat

variable {H : Type}

/-! ## Central morphisms -/

theorem aboveO_abrupt {top : List Val} {o : POut} (h : ¬ o.IsNormal) : aboveO top o = o := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;>
    first | rfl | exact absurd trivial h

theorem aboveO_normal_inv {top w : List Val} {o : POut}
    (h : POut.flow (.normal w) = aboveO top o) : ∃ ws, o = .flow (.normal ws) ∧ w = top ++ ws := by
  rcases o with (vs | ⟨l, vs⟩ | vs | _ | a) | ⟨a, args, n⟩ <;> simp [aboveO] at h
  exact ⟨vs, rfl, h⟩

theorem take_length_of_le {stk : List Val} {n : Nat} (h : n ≤ stk.length) :
    (stk.take n).length = n := by
  simp only [List.length_take]; omega

section Pure

variable {n n' : Nat} {φ : List Val → List Val} {g₁ g₂ : ORel H}

theorem lhs_iff (hp : PureAt n n' φ g₁) {s : Store H} {f : Frame} {stk : List Val}
    {s' : Store H} {f' : Frame} {o : POut} :
    seqR (leftR n g₁) (rightR n' g₂) s f stk s' f' o ↔
      n ≤ stk.length ∧ ∃ o₂, g₂ s f (stk.drop n) s' f' o₂ ∧ o = aboveO (φ (stk.take n)) o₂ := by
  constructor
  · rintro (⟨s₁, f₁, vs, ⟨hn, o₁, h₁, hv⟩, ⟨-, o₂, h₂, rfl⟩⟩ | ⟨⟨hn, o₁, h₁, rfl⟩, hnn⟩)
    · have hT := take_length_of_le hn
      obtain ⟨rfl, rfl, rfl⟩ := (hp.2 _ _ _ _ _ _ hT).1 h₁
      have hv' : vs = φ (stk.take n) ++ stk.drop n := by simpa [whiskO] using hv
      subst hv'
      have hl := hp.1 _ hT
      refine ⟨hn, o₂, ?_, ?_⟩
      · rwa [List.drop_left' hl] at h₂
      · rw [List.take_left' hl]
    · obtain ⟨-, -, rfl⟩ := (hp.2 _ _ _ _ _ _ (take_length_of_le hn)).1 h₁
      exact absurd trivial hnn
  · rintro ⟨hn, o₂, h₂, rfl⟩
    have hT := take_length_of_le hn
    have hl := hp.1 _ hT
    refine .inl ⟨s, f, φ (stk.take n) ++ stk.drop n,
      ⟨hn, _, (hp.2 _ _ _ _ _ _ hT).2 ⟨rfl, rfl, rfl⟩, rfl⟩, ⟨by simp [hl], o₂, ?_, ?_⟩⟩
    · rwa [List.drop_left' hl]
    · rw [List.take_left' hl]

theorem rhs_iff (hp : PureAt n n' φ g₁) {s : Store H} {f : Frame} {stk : List Val}
    {s' : Store H} {f' : Frame} {o : POut} :
    seqR (rightR n g₂) (leftR n g₁) s f stk s' f' o ↔
      n ≤ stk.length ∧ ∃ o₂, g₂ s f (stk.drop n) s' f' o₂ ∧ o = aboveO (φ (stk.take n)) o₂ := by
  constructor
  · rintro (⟨s₁, f₁, vs, ⟨hn, o₂, h₂, hv⟩, ⟨-, o₁, h₁, rfl⟩⟩ | ⟨⟨hn, o₂, h₂, rfl⟩, hnn⟩)
    · have hT := take_length_of_le hn
      obtain ⟨ws, rfl, rfl⟩ := aboveO_normal_inv hv
      rw [List.take_left' hT] at h₁
      obtain ⟨rfl, rfl, rfl⟩ := (hp.2 _ _ _ _ _ _ hT).1 h₁
      refine ⟨hn, _, h₂, ?_⟩
      rw [List.drop_left' hT]
      rfl
    · refine ⟨hn, o₂, h₂, ?_⟩
      have hn₂ : ¬ o₂.IsNormal := fun hN => by
        obtain ⟨ws, rfl⟩ := isNormal_inv hN
        exact hnn trivial
      rw [aboveO_abrupt hn₂, aboveO_abrupt hn₂]
  · rintro ⟨hn, o₂, h₂, rfl⟩
    have hT := take_length_of_le hn
    by_cases hN : o₂.IsNormal
    · obtain ⟨ws, rfl⟩ := isNormal_inv hN
      refine .inl ⟨s', f', stk.take n ++ ws, ⟨hn, _, h₂, rfl⟩,
        ⟨by simp; omega, .flow (.normal (φ (stk.take n))), ?_, ?_⟩⟩
      · rw [List.take_left' hT]
        exact (hp.2 _ _ _ _ _ _ hT).2 ⟨rfl, rfl, rfl⟩
      · rw [List.drop_left' hT]
        rfl
    · refine .inr ⟨⟨hn, o₂, h₂, ?_⟩, ?_⟩
      · rw [aboveO_abrupt hN, aboveO_abrupt hN]
      · rw [aboveO_abrupt hN]; exact hN

/-- **Pure morphisms are central.** -/
theorem interchange_of_pure (hp : PureAt n n' φ g₁) (g₂ : ORel H) : Interchange n n' g₁ g₂ := by
  funext s f stk s' f' o
  exact propext ((lhs_iff hp).trans (rhs_iff hp).symm)

end Pure

theorem pureAt_nil {C : Abstract.CallRel H} (n : Nat) : PureAt n n id (denR C []) := by
  refine ⟨fun _ h => h, fun s f stk s' f' o _ => ?_⟩
  rw [denR_nil]
  rfl

theorem pureAt_intConst {C : Abstract.CallRel H} (t : IntType) (b : BitVec t.width) :
    PureAt 0 1 (fun _ => [ofInt t b]) (denR C [.op (.intConst t b) []]) := by
  refine ⟨fun _ _ => rfl, fun s f stk s' f' o hl => ?_⟩
  rw [List.length_eq_zero_iff] at hl
  subst hl
  constructor
  · intro h
    cases h with
    | argsAbort hargs ho => cases hargs; exact absurd trivial ho
    | opOk hi hargs hflat hk =>
      cases hargs
      simp only [evalFlat, Option.some.injEq, Prod.mk.injEq, Flow.normal.injEq] at hflat
      obtain ⟨rfl, rfl, rfl⟩ := hflat
      cases hk
      exact ⟨rfl, rfl, rfl⟩
    | opStop hi hargs hflat hfl =>
      cases hargs
      simp only [evalFlat, Option.some.injEq, Prod.mk.injEq] at hflat
      obtain ⟨rfl, rfl, rfl⟩ := hflat
      exact absurd trivial hfl
    | tail _ hres => cases hres
    | tailRes _ hres => cases hres
  · rintro ⟨rfl, rfl, rfl⟩
    exact .opOk (fun x h => by cases h) .nil rfl .nil

/-! ## The interchange law fails for calls -/

namespace Ex

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

/-- The store context: no tags, two host functions of type `[] → []`. -/
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

theorem thom_callE (x : Fin (2 ^ 32)) (hx : x.val < 2) : THom Γ₀ I₀ I₀ (callE x) := by
  have hf : I₀.C.funcs[(⟨x⟩ : FuncIdx).toNat]? = some d₀ := by
    show [d₀, d₀][x.val]? = some d₀
    rcases x with ⟨_ | _ | x, h⟩
    · rfl
    · rfl
    · change x + 1 + 1 < 2 at hx
      omega
  exact Silmaril.Proofs.Wasm.Abstract.TypedCat.thom_call coh₀ (ps := .nil) (rs := .nil) (pre := [])
    rfl (fun t ht => by cases ht) hf he₀

theorem storeOk₀ : StoreOk s₀ where
  tags := by simp [s₀]
  globals := by simp [s₀]
  mems := by simp [s₀]
  tables := by simp [s₀]
  funcs := by
    intro fi h
    obtain rfl : fi = fi₀ := by simpa [s₀] using h
    exact .host tyOk₀ he₀ rfl
  elems := by simp [s₀]
  structs := by simp [s₀]
  arrays := by simp [s₀]
  exns := by simp [s₀]
  acyclicStructs := by simp [s₀]
  acyclicArrays := by simp [s₀]
  acyclicExns := by simp [s₀]
  structsClosed := by simp [s₀]
  arraysClosed := by simp [s₀]

theorem moduleInstOk₀ : ModuleInstOk s₀ mi₀
    { types := mi₀.types, recs := [], tags := [], globals := [], mems := [], tables := [],
      funcs := [d₀, d₀], datas := mi₀.datas.map fun _ => (), elems := [],
      refs := List.range 0 } :=
  .mk (tags := []) (globals := []) (mems := []) (tables := []) (funcs := [d₀, d₀]) (elems := [])
    (k := 0) (by simp [mi₀]) .nil .nil
    (.cons (ExternAddrOk.func (fi := fi₀) (rfl : s₀.funcs[0]? = some fi₀))
      (.cons (ExternAddrOk.func (fi := fi₀) (rfl : s₀.funcs[1]? = some fi₀)) .nil))
    .nil .nil (by simp [mi₀]) .nil (by simp [mi₀]) (by simp [mi₀]) (by simp [mi₀])
    (Nat.zero_le _)

theorem realizes₀ : Realizes Γ₀ I₀ s₀ f₀ [] := by
  refine ⟨⟨rfl, rfl, fun a e h => by simp [s₀] at h⟩, storeOk₀, rfl,
    ⟨_, ⟨_, [], moduleInstOk₀, .nil, rfl⟩, rfl⟩, ⟨[], rfl, fun t ht => by cases ht⟩,
    fun L hL => by simp [I₀, ctx₀] at hL, .nil⟩

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

theorem orders_differ :
    seqR (leftR 0 (denR C₀ (callE 0))) (rightR 0 (denR C₀ (callE 1))) s₀ f₀ []
        (mark (mark s₀ 0) 1) f₀ (.flow (.normal [])) ∧
      ¬ seqR (rightR 0 (denR C₀ (callE 1))) (leftR 0 (denR C₀ (callE 0))) s₀ f₀ []
        (mark (mark s₀ 0) 1) f₀ (.flow (.normal [])) := by
  refine ⟨.inl ⟨mark s₀ 0, f₀, [], ⟨le_refl _, _, call_run rfl rfl, rfl⟩,
    ⟨le_refl _, _, call_run rfl rfl, rfl⟩⟩, ?_⟩
  rintro (⟨s₁, f₁, vs, ⟨-, o₂, h₂, hv⟩, ⟨-, o₁, h₁, -⟩⟩ | ⟨-, hn⟩)
  · obtain ⟨rfl, rfl, rfl⟩ := call_inv (x := ⟨1⟩) (a₀ := 1) rfl h₂
    simp [aboveO] at hv
    subst hv
    obtain ⟨h1, -, -⟩ := call_inv (x := ⟨0⟩) (a₀ := 0) rfl h₁
    have := congrArg Store.elems h1
    simp [mark, s₀] at this
  · exact absurd trivial hn

/-- **The interchange law fails for typed calls.** -/
theorem not_interchange :
    ∃ (Γ : Ctx Unit) (C : Abstract.CallRel Unit) (I : TIface) (e₁ e₂ : List BExpr)
      (s : Store Unit) (f : Frame),
      TypedAns Γ C ∧ ArityResp Γ C ∧ Coh Γ I ∧ THom Γ I I e₁ ∧ THom Γ I I e₂ ∧
        Realizes Γ I s f [] ∧
        (∃ s' f' o, seqR (leftR 0 (denR C e₁)) (rightR 0 (denR C e₂)) s f [] s' f' o ∧
          ¬ seqR (rightR 0 (denR C e₂)) (leftR 0 (denR C e₁)) s f [] s' f' o) ∧
        ¬ Interchange 0 0 (denR C e₁) (denR C e₂) :=
  ⟨Γ₀, C₀, I₀, callE 0, callE 1, s₀, f₀, typedAns₀, arityResp_of_typedAns typedAns₀, coh₀,
    thom_callE 0 (by decide), thom_callE 1 (by decide), realizes₀,
    ⟨_, _, _, orders_differ.1, orders_differ.2⟩,
    fun h => orders_differ.2 (by unfold Interchange at h; rw [← h]; exact orders_differ.1)⟩

end Ex

end Silmaril.Proofs.Wasm.Abstract.TypedCat
