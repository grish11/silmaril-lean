module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Ghost
public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Scrub
public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Ctx

@[expose] public section

/-!
# The witness after an allocation (proofs)

A Wasm `throw` allocates `e` at `n = s.exns.length`; the witness step allocates it at
`N = X.length`, so `gst (s.addExn e) T (X ++ [e])` is typed but no witness of `s.addExn e`
(address `n` is a pad there). `alloc_ghost` builds the witness of `s.addExn e`: `e` moves to
address `n`, the pad of `n` moves to `N`, and every exception field is redirected to `N`
(`scrubE N`). Redirection is needed: with aliasing, `e` may contain `ref.exn n` itself
(`DanglingExn.not_storeOk_addExn_self`).

The new witness is `StoreOk`: typing transfers (`Widen`); a cycle through `n` would need a field
naming `n` (none: exception fields name `N`, struct and array fields name exceptions of `s`,
`HeapBelow`); `N` has no fields; and every other path is one of the typed witness.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (ContextTyped)

variable {H : Type}

/-- **Struct and array fields name exceptions of the store** (also under `extern`). -/
def HeapBelow (s : Store H) : Prop :=
  (∀ si ∈ s.structs, ∀ r, FieldVal.val (.ref r) ∈ si.fields → RefLeaves (· < s.exns.length) r) ∧
    ∀ ai ∈ s.arrays, ∀ r, FieldVal.val (.ref r) ∈ ai.fields → RefLeaves (· < s.exns.length) r

section Alloc

variable {s : Store H} {T : List TagInst} {X : List ExnInst} {e p : ExnInst}

/-- The exception list of the witness after allocating `e`, with the pad `p` moved to the end. -/
def allocX (X : List ExnInst) (n : Nat) (e p : ExnInst) : List ExnInst :=
  (X.set n e ++ [p]).map (scrubE X.length)

theorem allocX_length (n : Nat) : (allocX X n e p).length = X.length + 1 := by simp [allocX]

theorem allocX_get_n {n : Nat} (hn : n < X.length) :
    (allocX X n e p)[n]? = some (scrubE X.length e) := by
  simp only [allocX, List.getElem?_map]
  rw [List.getElem?_append_left (by simpa using hn)]
  simp [hn]

theorem allocX_get_N (n : Nat) : (allocX X n e p)[X.length]? = some (scrubE X.length p) := by
  simp only [allocX, List.getElem?_map]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem allocX_get_ne {n a : Nat} (ha : a ≠ n) (hlt : a < X.length) :
    (allocX X n e p)[a]? = X[a]?.map (scrubE X.length) := by
  simp only [allocX, List.getElem?_map]
  rw [List.getElem?_append_left (by simpa using hlt), List.getElem?_set_ne (Ne.symm ha)]

theorem allocX_get_gt {n a : Nat} (hgt : X.length < a) : (allocX X n e p)[a]? = none := by
  rw [List.getElem?_eq_none]
  rw [allocX_length]; omega

end Alloc

section Paths

variable {s : Store H} {T : List TagInst} {X : List ExnInst} {e p : ExnInst}

local notation "g₁" => gst (s.addExn e) T (X ++ [e])
local notation "g'" => gst (s.addExn e) T (allocX X s.exns.length e p)

/-- A field value that is a chain to `a`. -/
def FChain (a : Nat) (fv : FieldVal) : Prop := ∃ r, fv = .val (.ref r) ∧ ChainTo a r

variable (hn : s.exns.length < X.length) (hpf : p.fields = []) (hheap : HeapBelow s)
include hn hpf hheap

omit hheap in
theorem g'_exn {a : Nat} {x : ExnInst} (h : (g').exns[a]? = some x) :
    (a = s.exns.length ∧ x = scrubE X.length e) ∨ (a = X.length ∧ x.fields = []) ∨
      (a ≠ s.exns.length ∧ a < X.length ∧ ∃ y, X[a]? = some y ∧ x = scrubE X.length y) := by
  have h' : (allocX X s.exns.length e p)[a]? = some x := h
  by_cases ha : a = s.exns.length
  · subst ha
    rw [allocX_get_n hn] at h'
    exact .inl ⟨rfl, (Option.some.inj h').symm⟩
  · rcases Nat.lt_trichotomy a X.length with hlt | rfl | hgt
    · rw [allocX_get_ne ha hlt, Option.map_eq_some_iff] at h'
      obtain ⟨y, hy, rfl⟩ := h'
      exact .inr (.inr ⟨ha, hlt, y, hy, rfl⟩)
    · rw [allocX_get_N] at h'
      cases h'
      exact .inr (.inl ⟨rfl, by simp [scrubE, hpf]⟩)
    · rw [allocX_get_gt hgt] at h'; cases h'

omit hn hpf hheap in
theorem fields_scrub_chain {y : ExnInst} {v : Val} (hv : v ∈ (scrubE X.length y).fields)
    {a : Nat} (hc : FChain a (.val v)) : a = X.length := by
  obtain ⟨r, he, hr⟩ := hc
  cases he
  simp only [scrubE, List.mem_map] at hv
  obtain ⟨w, -, hw⟩ := hv
  cases w <;> simp [scrubV] at hw
  subst hw
  exact chainTo_scrubR hr

/-- (A) Only an `extern` chain to `n` reaches a chain to `n`. -/
theorem reach_chain_n {u w : FieldVal} (h : ImmutReachable g' u w) :
    FChain s.exns.length w → ∃ r, u = .val (.ref (.extern r)) ∧ ChainTo s.exns.length r := by
  induction h with
  | trans _ _ ih₁ ih₂ =>
    intro hw
    obtain ⟨r, rfl, hr⟩ := ih₂ hw
    exact ih₁ ⟨_, rfl, hr⟩
  | @refStruct a i si fs z fv hs _ _ hfv =>
    rintro ⟨r, rfl, hr⟩
    exact absurd hr (not_chainTo_of_leaves
      (hheap.1 si (List.mem_of_getElem? hs) r (List.mem_of_getElem? hfv)))
  | @refArray a i ai z fv hs _ hfv =>
    rintro ⟨r, rfl, hr⟩
    exact absurd hr (not_chainTo_of_leaves
      (hheap.2 ai (List.mem_of_getElem? hs) r (List.mem_of_getElem? hfv)))
  | @refExn a i x v hs hv =>
    intro hw
    rcases g'_exn hn hpf hs with ⟨-, rfl⟩ | ⟨-, hx⟩ | ⟨-, -, y, -, rfl⟩
    · have := fields_scrub_chain (List.mem_of_getElem? hv) hw; omega
    · rw [hx] at hv; simp at hv
    · have := fields_scrub_chain (List.mem_of_getElem? hv) hw; omega
  | refExtern r =>
    rintro ⟨r', he, hr⟩
    cases he
    exact ⟨_, rfl, hr⟩

omit hheap in
/-- (C) The pad at `N` reaches nothing. -/
theorem reach_from_N {u w : FieldVal} (h : ImmutReachable g' u w) :
    u = .val (.ref (.exn X.length)) → False := by
  induction h with
  | trans _ _ ih₁ _ => exact ih₁
  | refStruct => intro he; cases he
  | refArray => intro he; cases he
  | @refExn a i x v hs hv =>
    intro he
    cases he
    rcases g'_exn hn hpf hs with ⟨ha, -⟩ | ⟨-, hx⟩ | ⟨-, hlt, -⟩
    · omega
    · rw [hx] at hv; simp at hv
    · omega
  | refExtern r => intro he; cases he

omit hheap in
/-- (C') From a chain to `N` only chains to `N` are reached. -/
theorem reach_chain_N {u w : FieldVal} (h : ImmutReachable g' u w) :
    FChain X.length u → FChain X.length w := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact fun hu => ih₂ (ih₁ hu)
  | refStruct => rintro ⟨r, he, hr⟩; cases he; exact hr.elim
  | refArray => rintro ⟨r, he, hr⟩; cases he; exact hr.elim
  | @refExn a i x v hs hv =>
    rintro ⟨r, he, hr⟩
    cases he
    simp only [ChainTo] at hr
    subst hr
    rcases g'_exn hn hpf hs with ⟨ha, -⟩ | ⟨-, hx⟩ | ⟨-, hlt, -⟩
    · omega
    · rw [hx] at hv; simp at hv
    · omega
  | refExtern r => rintro ⟨r', he, hr⟩; cases he; exact ⟨r, rfl, hr⟩

/-- (D) Every other path is a path of the typed witness. -/
theorem reach_back {u w : FieldVal} (h : ImmutReachable g' u w) :
    ¬ FChain s.exns.length u → ¬ FChain X.length w → ImmutReachable g₁ u w := by
  induction h with
  | @trans u v w h₁ h₂ ih₁ ih₂ =>
    intro hu hw
    have hv₁ : ¬ FChain s.exns.length v := fun hv => by
      obtain ⟨r, rfl, hr⟩ := reach_chain_n hn hpf hheap h₁ hv
      exact hu ⟨_, rfl, hr⟩
    have hv₂ : ¬ FChain X.length v := fun hv => hw (reach_chain_N hn hpf h₂ hv)
    exact .trans (ih₁ hu hv₂) (ih₂ hv₁ hw)
  | refStruct hs he hi hfv => intro _ _; exact .refStruct hs he hi hfv
  | refArray hs he hfv => intro _ _; exact .refArray hs he hfv
  | @refExn a i x v hs hv =>
    intro hu hw
    rcases g'_exn hn hpf hs with ⟨ha, -⟩ | ⟨-, hx⟩ | ⟨-, hlt, y, hy, rfl⟩
    · exact absurd ⟨_, rfl, ha⟩ hu
    · rw [hx] at hv; simp at hv
    · have hy' : (g₁).exns[a]? = some y := by
        show (X ++ [e])[a]? = some y
        rw [List.getElem?_append_left hlt]; exact hy
      simp only [scrubE, List.getElem?_map, Option.map_eq_some_iff] at hv
      obtain ⟨v₀, hv₀, rfl⟩ := hv
      cases v₀ with
      | ref r =>
        rcases scrubR_cases X.length r with h | h
        · simp only [scrubV, h]; exact .refExn hy' hv₀
        · exact absurd ⟨_, rfl, h⟩ hw
      | _ => exact .refExn hy' hv₀
  | refExtern r => intro _ _; exact .refExtern r

end Paths

theorem forall₂_map_right {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop} {g : β → γ}
    (hg : ∀ a b, R a b → S a (g b)) : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ S l₁ (l₂.map g)
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (hg _ _ h) (forall₂_map_right hg hs)

theorem forall₂_map_left {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop} {g : α → γ}
    (hg : ∀ a b, R a b → S (g a) b) : ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ S (l₁.map g) l₂
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (hg _ _ h) (forall₂_map_left hg hs)

theorem forall₂_map_right_mem {α β γ : Type} {R : α → β → Prop} {S : α → γ → Prop}
    {g : β → γ} : ∀ {l₁ : List α} {l₂ : List β}, (∀ a b, b ∈ l₂ → R a b → S a (g b)) →
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ (l₂.map g)
  | _, _, _, .nil => .nil
  | _, _, hg, .cons h hs => .cons (hg _ _ (List.mem_cons_self ..) h)
      (forall₂_map_right_mem (fun a b hb => hg a b (List.mem_cons_of_mem _ hb)) hs)

theorem forall₂_map_self {α β : Type} {S : α → β → Prop} {g : α → β} :
    ∀ {l : List α}, (∀ a ∈ l, S a (g a)) → List.Forall₂ S l (l.map g)
  | [], _ => .nil
  | a :: _, h => .cons (h a (List.mem_cons_self ..))
      (forall₂_map_self fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ a ∈ l₁, ∃ b, R a b
  | _, _, .nil, _, h => nomatch h
  | _, _, .cons h hs, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, h⟩
    · exact forall₂_mem_left hs a ha

theorem leaves_of_valOk {s : Store H} {v : Val} {t : CValType} (h : ValOk s v t) :
    ∀ r, v = .ref r → RefLeaves (· < s.exns.length) r := by
  intro r hr
  subst hr
  cases h with
  | ref h => exact refLeaves_of_refOk h

theorem exnInstOk_scrub {s t : Store H} (hw : Widen s t) {N : Nat} {z : ExnInst}
    (hN : t.exns[N]? = some z) {y : ExnInst} (h : ExnInstOk s y) : ExnInstOk t (scrubE N y) := by
  obtain ⟨ti, ts, htag, hexp, hfs⟩ := h
  exact ⟨ti, ts, hw.tag? htag, hexp,
    forall₂_map_left (fun v t' hv => valOk_scrub hN (hw.valOk hv)) hfs⟩

/-- **The witness after an allocation.** -/
theorem alloc_ghost {s : Store H} {T : List TagInst} {X : List ExnInst} {f : Frame}
    {es : List Admin} {e : ExnInst} (hg : GhostOk s T X) (hheap : HeapBelow s)
    (ht : ContextTyped ⟨gst (s.addExn e) T (X ++ [e]), f, es⟩) :
    ∃ X', X'.length = X.length + 1 ∧ GhostOk (s.addExn e) T X' ∧
      ContextTyped ⟨gst (s.addExn e) T X', f, es⟩ := by
  obtain ⟨p, hp⟩ : ∃ p, X[s.exns.length]? = some p :=
    ⟨_, List.getElem?_eq_getElem hg.lt⟩
  have hpad := hg.pad _ p (Nat.le_refl _) hp
  have hn := hg.lt
  have hS₁ : StoreOk (gst (s.addExn e) T (X ++ [e])) := storeOk_of_contextTyped ht
  have hlen : (allocX X s.exns.length e p).length = X.length + 1 := allocX_length _
  have hw : Widen (gst (s.addExn e) T (X ++ [e]))
      (gst (s.addExn e) T (allocX X s.exns.length e p)) := by
    refine ⟨rfl, List.prefix_refl _, fun a y hy => ?_⟩
    have ha : a < (X ++ [e]).length := (List.getElem?_eq_some_iff.1 hy).1
    exact ⟨_, List.getElem?_eq_getElem (l := allocX X s.exns.length e p)
      (by rw [hlen]; simpa using ha)⟩
  have hN : (gst (s.addExn e) T (allocX X s.exns.length e p)).exns[X.length]? =
      some (scrubE X.length p) := allocX_get_N _
  have hmem : ∀ x ∈ allocX X s.exns.length e p, ∃ y ∈ X ++ [e], x = scrubE X.length y := by
    intro x hx
    simp only [allocX, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    rcases List.mem_append.1 hy with hy | hy
    · rcases List.mem_or_eq_of_mem_set hy with hy | rfl
      · exact List.mem_append_left _ hy
      · exact List.mem_append_right _ (List.mem_singleton_self _)
    · rw [List.mem_singleton.1 hy]
      exact List.mem_append_left _ (List.mem_of_getElem? hp)
  have hS' : StoreOk (gst (s.addExn e) T (allocX X s.exns.length e p)) := by
    refine ⟨hS₁.tags, fun gi h => hw.globalInstOk (hS₁.globals gi h), hS₁.mems,
      fun ti h => hw.tableInstOk (hS₁.tables ti h), fun fi h => hw.funcInstOk (hS₁.funcs fi h),
      fun ei h => hw.elemInstOk (hS₁.elems ei h), fun si h => hw.structInstOk (hS₁.structs si h),
      fun ai h => hw.arrayInstOk (hS₁.arrays ai h), ?_, ?_, ?_, ?_, hS₁.structsClosed,
      hS₁.arraysClosed⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hmem x hx
      exact exnInstOk_scrub hw hN (hS₁.exns y hy)
    · intro a ha hr
      refine hS₁.acyclicStructs a ha (reach_back hn hpad.2 hheap hr ?_ ?_)
      · rintro ⟨r, he, hc⟩; cases he; exact hc
      · rintro ⟨r, he, hc⟩; cases he; exact hc
    · intro a ha hr
      refine hS₁.acyclicArrays a ha (reach_back hn hpad.2 hheap hr ?_ ?_)
      · rintro ⟨r, he, hc⟩; cases he; exact hc
      · rintro ⟨r, he, hc⟩; cases he; exact hc
    · intro a ha hr
      by_cases han : a = s.exns.length
      · subst han
        obtain ⟨r, he, -⟩ := reach_chain_n hn hpad.2 hheap hr ⟨_, rfl, rfl⟩
        cases he
      · by_cases haN : a = X.length
        · subst haN; exact reach_from_N hn hpad.2 hr rfl
        · refine hS₁.acyclicExns a (by simpa [hlen] using ha)
            (reach_back hn hpad.2 hheap hr ?_ ?_)
          · rintro ⟨r, he, hc⟩; cases he; exact han hc
          · rintro ⟨r, he, hc⟩; cases he; exact haN hc
  have hleaves : ∀ y ∈ X ++ [e], ∀ v ∈ y.fields, ∀ r, v = .ref r →
      RefLeaves (· < X.length + 1) r := by
    intro y hy v hv r hr
    obtain ⟨ti, ts, -, -, hfs⟩ := hS₁.exns y hy
    obtain ⟨t, hvt⟩ := forall₂_mem_left hfs v hv
    simpa using leaves_of_valOk hvt r hr
  refine ⟨_, hlen, ⟨hg.tags, by simpa [Store.addExn, hlen] using hn, ?_, ?_⟩,
    contextTyped_widen hw hS' ht⟩
  · rw [hlen]
    intro a x hx
    by_cases hlt : a < s.exns.length
    · have hx' : s.exns[a]? = some x := by
        simpa [Store.addExn, List.getElem?_append_left hlt] using hx
      obtain ⟨y, hy, htag, hfs⟩ := hg.real a x hx'
      refine ⟨scrubE X.length y, ?_, htag, ?_⟩
      · rw [allocX_get_ne (Nat.ne_of_lt hlt) (Nat.lt_trans hlt hn), hy]; rfl
      · exact forall₂_map_right_mem (fun v w hw' h => valApprox_scrub (h.mono (by omega))
          (hleaves y (List.mem_append_left _ (List.mem_of_getElem? hy)) w hw')) hfs
    · have ha : a = s.exns.length := by
        have := (List.getElem?_eq_some_iff.1 hx).1
        simp [Store.addExn] at this; omega
      subst ha
      have hx' : x = e := by simp [Store.addExn] at hx; exact hx.symm
      subst hx'
      refine ⟨scrubE X.length x, allocX_get_n hn, rfl, forall₂_map_self fun v hv =>
        valApprox_scrub (.inl rfl) (hleaves x (List.mem_append_right _ (List.mem_singleton_self _))
          v hv)⟩
  · intro a x ha hx
    simp only [Store.addExn, List.length_append, List.length_singleton] at ha
    rcases Nat.lt_trichotomy a X.length with hlt | rfl | hgt
    · rw [allocX_get_ne (by omega) hlt, Option.map_eq_some_iff] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have := hg.pad a y (by omega) hy
      exact ⟨this.1, by simp [scrubE, this.2]⟩
    · rw [allocX_get_N] at hx
      cases hx
      exact ⟨hpad.1, by simp [scrubE, hpad.2]⟩
    · rw [allocX_get_gt hgt] at hx; cases hx

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
