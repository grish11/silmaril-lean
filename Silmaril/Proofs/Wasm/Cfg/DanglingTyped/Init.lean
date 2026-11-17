module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Run
public import Silmaril.Wasm.V1.ToCore.DefTypes
public import Silmaril.Wasm.Validation.Check.TyOk
public import Silmaril.Wasm.Execution.Core.Soundness

@[expose] public section

/-!
# The relaxed store invariant; typed stores and invocations (proofs)

`StoreOkD s`: supported functions, struct and array fields naming exceptions of `s`, and a typing
witness `gst s T X` that is `StoreOk`. It is what a round leaves (`storeOkD_of_configOkD`),
including stores with a dangling reference in a global or a self-referencing exception, which are
not `StoreOk` (`DanglingExn.not_storeOk_of_global`, `not_storeOk_addExn_self`).

* `storeOkD_of_storeOk`: a `StoreOk` store with supported functions is `StoreOkD`; its witness
  adds one fresh tag `padTag` (`[] → []`) and one pad exception of that tag;
* `configOkD_invoke`: an invocation typed on the witness (`InvokeOk`) is `ConfigOkD`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm.Cfg.DanglingTyped
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (ContextTyped)

variable {H : Type}

/-- The type `[] → []` of the fresh tag of a witness. -/
def padTy : DefType := (⟨[], []⟩ : V1.FuncType).toDefType

/-- The fresh tag of a witness. -/
def padTag : TagInst := ⟨padTy⟩

theorem padTag_ok : TagInstOk padTag := TagTypeOk.check_sound (by decide)

theorem padTy_expand : Expand padTy (.func (Ty.ofList []) .nil) := Expand.iff.2 (by decide)

theorem storeOkD_of_configOkD {c : Config H} (h : ConfigOkD c) : StoreOkD c.store := by
  obtain ⟨hF, -, -, hheap, T, X, hg, hct⟩ := h
  exact ⟨hF, hheap, T, X, hg, storeOk_of_contextTyped hct⟩

theorem heapBelow_of_storeOk {s : Store H} (hs : StoreOk s) : HeapBelow s := by
  refine ⟨fun si hsi r hr => ?_, fun ai hai r hr => ?_⟩
  · obtain ⟨fs, -, hfs⟩ := hs.structs si hsi
    obtain ⟨t, ht⟩ := forall₂_mem_left hfs _ hr
    cases ht with
    | val h => exact leaves_of_valOk h r rfl
  · obtain ⟨ft, -, hfs⟩ := hs.arrays ai hai
    have h := hfs _ hr
    generalize fieldStorage ft = st at h
    cases h with
    | val h => exact leaves_of_valOk h r rfl

theorem reach_pad {s : Store H} {p : ExnInst} (hp : p.fields = []) {u w : FieldVal}
    (h : ImmutReachable (gst s (s.tags ++ [padTag]) (s.exns ++ [p])) u w) :
    ImmutReachable s u w := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct hs he hi hfv
  | refArray hs he hfv => exact .refArray hs he hfv
  | @refExn a i x v hs hv =>
    have hs' : (s.exns ++ [p])[a]? = some x := hs
    rcases Nat.lt_or_ge a s.exns.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hs'
      exact .refExn hs' hv
    · rw [List.getElem?_append_right hge] at hs'
      have : x = p := by
        have h1 := (List.getElem?_eq_some_iff.1 hs').1
        simp at h1
        simpa [show a - s.exns.length = 0 by omega] using hs'.symm
      subst this
      rw [hp] at hv; simp at hv
  | refExtern r => exact .refExtern r

theorem not_reach_beyond_s {s : Store H} {a : Nat} (ha : s.exns.length ≤ a) {u w : FieldVal}
    (h : ImmutReachable s u w) : u ≠ .val (.ref (.exn a)) := by
  induction h with
  | trans _ _ ih₁ _ => exact ih₁
  | refExn hs _ =>
    intro he
    cases he
    have := (List.getElem?_eq_some_iff.1 hs).1
    omega
  | _ => intro he; cases he

/-- **A typed store with supported functions satisfies the relaxed store invariant.** -/
theorem storeOkD_of_storeOk {s : Store H} (hs : StoreOk s) (hF : FuncsSupp s) : StoreOkD s := by
  let p : ExnInst := ⟨s.tags.length, []⟩
  have hw : Widen s (gst s (s.tags ++ [padTag]) (s.exns ++ [p])) :=
    ⟨rfl, List.prefix_append _ _, fun a y hy => ⟨y, by
      show (s.exns ++ [p])[a]? = _
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hy).1]; exact hy⟩⟩
  refine ⟨hF, heapBelow_of_storeOk hs, s.tags ++ [padTag], s.exns ++ [p], ⟨List.prefix_append _ _,
    by simp, fun a e he => ⟨e, ?_, rfl, ?_⟩, fun a e' ha he' => ?_⟩, ?_⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 he).1]; exact he
  · have := forall₂_map_self (S := ValApprox (s.exns ++ [p]).length) (g := id) (l := e.fields)
      (fun _ _ => Or.inl rfl)
    simpa using this
  · have h1 := (List.getElem?_eq_some_iff.1 he').1
    simp at h1
    rw [List.getElem?_append_right ha] at he'
    have : e' = p := by simpa [show a - s.exns.length = 0 by omega] using he'.symm
    subst this
    exact ⟨Nat.le_refl _, rfl⟩
  · refine ⟨?_, fun gi h => hw.globalInstOk (hs.globals gi h), hs.mems,
      fun ti h => hw.tableInstOk (hs.tables ti h), fun fi h => hw.funcInstOk (hs.funcs fi h),
      fun ei h => hw.elemInstOk (hs.elems ei h), fun si h => hw.structInstOk (hs.structs si h),
      fun ai h => hw.arrayInstOk (hs.arrays ai h), ?_,
      fun a ha hr => hs.acyclicStructs a ha (reach_pad rfl hr),
      fun a ha hr => hs.acyclicArrays a ha (reach_pad rfl hr), ?_, hs.structsClosed,
      hs.arraysClosed⟩
    · intro ti hti
      rcases List.mem_append.1 hti with h | h
      · exact hs.tags ti h
      · rw [List.mem_singleton.1 h]; exact padTag_ok
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · obtain ⟨ti, ts, h1, h2, h3⟩ := hs.exns x h
        exact ⟨ti, ts, hw.tag? h1, h2, h3.imp fun _ _ h => hw.valOk h⟩
      · rw [List.mem_singleton.1 h]
        refine ⟨padTag, Ty.ofList [], ?_, padTy_expand, by simp [p]⟩
        show (s.tags ++ [padTag])[s.tags.length]? = some padTag
        simp
    · intro a ha hr
      have hr' := reach_pad rfl hr
      rcases Nat.lt_or_ge a s.exns.length with hlt | hge
      · exact hs.acyclicExns a hlt hr'
      · exact not_reach_beyond_s hge hr' rfl

/-- **A typed invocation from a relaxed store satisfies the relaxed invariant.** The invocation is
typed on a witness of the store. -/
theorem configOkD_invoke {s : Store H} {T : List TagInst} {X : List ExnInst} (hF : FuncsSupp s)
    (hheap : HeapBelow s) (hg : GhostOk s T X) (hS : StoreOk (gst s T X)) {a : Nat}
    {vs : List Val} (hok : InvokeOk (gst s T X) a vs) : ConfigOkD (invoke s a vs) := by
  obtain ⟨fi₀, ps₀, rs₀, -, -, hcok⟩ := invoke_ok hS hok
  have hct := Sim.ContextTyped.of_configOk hcok
  have hinv : invoke (gst s T X) a vs = ⟨gst s T X, {}, (invoke s a vs).code⟩ := by
    simp [invoke]
  rw [hinv] at hct
  refine ⟨hF, fun t ht => by simp [invoke] at ht, ?_, hheap, T, X, hg, by simpa [invoke] using hct⟩
  intro x hx
  simp only [invoke, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | rfl | rfl
  · exact asupp_vals vs x hx
  · exact .ref _
  · exact .callRefType _

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
