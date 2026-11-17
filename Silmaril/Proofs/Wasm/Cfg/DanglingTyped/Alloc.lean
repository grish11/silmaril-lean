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

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
