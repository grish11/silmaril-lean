module

public import Silmaril.Wasm.Abstract.HostClosing.Defs
public import Silmaril.Wasm.Abstract.HostEval.Thms

/-!
# Call logs resolved with host imports (proofs)

The bookkeeping of `Closing/Basic` with import logs: against a closed module `c` of
`wasmHShape`, a recorded internal call returns (`RetL`), traps (`TrapsL`) or diverges
(`DivsL`) after the import calls `q` of the callee's behaviour; resolving a whole log
concatenates them (`AllRetL`, `TrapAtL`), and `Shape.Subst` on a lifted log is exactly this
(`substL_cases`, `subst_of_allRetL`, `subst_of_trapAtL`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosing

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

/-- Import calls of the host signature. -/
abbrev ICall (H : Type) : Type := Call (wasmHostSig H)

/-- The recorded call returned with its answer, after the callee's import calls `q`. -/
def RetL (c : (wasmHShape H).ClosedMod) (z : OCall H) (q : List (ICall H)) : Prop :=
  ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ ∧ (q, .ret b s₂) ∈ c a s₁ args

/-- The recorded call traps, after the callee's import calls `q`. -/
def TrapsL (c : (wasmHShape H).ClosedMod) (z : OCall H) (q : List (ICall H)) : Prop :=
  ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ ∧ (q, .trap) ∈ c a s₁ args

/-- The recorded call diverges, after the callee's import calls `q`. -/
def DivsL (c : (wasmHShape H).ClosedMod) (z : OCall H) (q : List (ICall H)) : Prop :=
  ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ ∧ (q, .div) ∈ c a s₁ args

/-- Every recorded call returned; `q` is their import calls, in order. -/
inductive AllRetL (c : (wasmHShape H).ClosedMod) : List (OCall H) → List (ICall H) → Prop
  | nil : AllRetL c [] []
  | cons {z : OCall H} {l : List (OCall H)} {q₁ q₂ : List (ICall H)} :
      RetL c z q₁ → AllRetL c l q₂ → AllRetL c (z :: l) (q₁ ++ q₂)

/-- Some recorded call traps, all calls before it returned. -/
inductive TrapAtL (c : (wasmHShape H).ClosedMod) : List (OCall H) → List (ICall H) → Prop
  | here {z : OCall H} {l : List (OCall H)} {q : List (ICall H)} :
      TrapsL c z q → TrapAtL c (z :: l) q
  | there {z : OCall H} {l : List (OCall H)} {q₁ q₂ : List (ICall H)} :
      RetL c z q₁ → TrapAtL c l q₂ → TrapAtL c (z :: l) (q₁ ++ q₂)

theorem OCall.eq_mk (z : OCall H) : ∃ a args s₁ b s₂, z = OCall.mk a args s₁ b s₂ := by
  match z with
  | ⟨.inr ⟨a, args, s₁⟩, (b, s₂)⟩ => exact ⟨a, args, s₁, b, s₂, rfl⟩
  | ⟨.inl m, _⟩ => exact (m : PEmpty).elim

theorem OCall.mk_inj {a a' : Nat} {args args' : List Val} {s₁ s₁' : Store H}
    {b b' : List Val ⊕ Nat} {s₂ s₂' : Store H}
    (h : OCall.mk a args s₁ b s₂ = OCall.mk a' args' s₁' b' s₂') :
    a = a' ∧ args = args' ∧ s₁ = s₁' ∧ b = b' ∧ s₂ = s₂' := by
  unfold OCall.mk at h
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem lift_mk (a : Nat) (args : List Val) (s₁ : Store H) (b : List Val ⊕ Nat) (s₂ : Store H) :
    (OCall.mk a args s₁ b s₂).lift = ⟨.inr ⟨a, (args, s₁)⟩, (b, s₂)⟩ := rfl

theorem allRetL_append {c : (wasmHShape H).ClosedMod} {u v : List (OCall H)} {q : List (ICall H)} :
    AllRetL c (u ++ v) q ↔ ∃ q₁ q₂, q = q₁ ++ q₂ ∧ AllRetL c u q₁ ∧ AllRetL c v q₂ := by
  induction u generalizing q with
  | nil => exact ⟨fun h => ⟨[], q, rfl, .nil, h⟩, fun ⟨q₁, q₂, e, h₁, h₂⟩ => by cases h₁; simpa [e] using h₂⟩
  | cons z u ih =>
    constructor
    · intro h
      cases h with
      | cons hz h =>
        obtain ⟨q₁, q₂, rfl, h₁, h₂⟩ := ih.1 h
        exact ⟨_, q₂, by simp, .cons hz h₁, h₂⟩
    · rintro ⟨q₁, q₂, rfl, h₁, h₂⟩
      cases h₁ with
      | cons hz h₁ =>
        rw [List.append_assoc]
        exact .cons hz (ih.2 ⟨_, _, rfl, h₁, h₂⟩)

theorem allRetL_singleton {c : (wasmHShape H).ClosedMod} {z : OCall H} {q : List (ICall H)}
    (h : RetL c z q) : AllRetL c [z] q := by
  simpa using AllRetL.cons h .nil

theorem trapAtL_append_right {c : (wasmHShape H).ClosedMod} {u v : List (OCall H)}
    {q₁ q₂ : List (ICall H)} (hu : AllRetL c u q₁) (hv : TrapAtL c v q₂) :
    TrapAtL c (u ++ v) (q₁ ++ q₂) := by
  induction hu with
  | nil => simpa using hv
  | cons hz _ ih =>
    rw [List.append_assoc]
    exact .there hz ih

theorem trapAtL_append {c : (wasmHShape H).ClosedMod} {u v : List (OCall H)} {q : List (ICall H)}
    (h : TrapAtL c (u ++ v) q) :
    TrapAtL c u q ∨ ∃ q₁ q₂, q = q₁ ++ q₂ ∧ AllRetL c u q₁ ∧ TrapAtL c v q₂ := by
  induction u generalizing q with
  | nil => exact .inr ⟨[], q, rfl, .nil, h⟩
  | cons z u ih =>
    cases h with
    | here h => exact .inl (.here h)
    | there hz h =>
      rcases ih h with h | ⟨q₁, q₂, rfl, hu, hv⟩
      · exact .inl (.there hz h)
      · exact .inr ⟨_, q₂, by simp, .cons hz hu, hv⟩

theorem trapAtL_nil {c : (wasmHShape H).ClosedMod} {q : List (ICall H)} : ¬ TrapAtL c [] q := nofun

/-- Resolving a lifted log whose calls all return. -/
theorem subst_of_allRetL {c : (wasmHShape H).ClosedMod} {e : End (wasmHShape H).S (List Val ⊕ Nat)}
    {l : List (OCall H)} {q : List (ICall H)} (h : AllRetL c l q) :
    Shape.Subst c (l.map OCall.lift) e (q, e) := by
  induction h with
  | nil => exact .nil e
  | cons hz _ ih =>
    obtain ⟨a, args, s₁, b, s₂, rfl, hz⟩ := hz
    exact Shape.Subst.int hz ih

/-- Resolving a lifted log with a trapping call. -/
theorem subst_of_trapAtL {c : (wasmHShape H).ClosedMod} {e : End (wasmHShape H).S (List Val ⊕ Nat)}
    {l : List (OCall H)} {q : List (ICall H)} (h : TrapAtL c l q) :
    Shape.Subst c (l.map OCall.lift) e (q, .trap) := by
  induction h with
  | here hz =>
    obtain ⟨a, args, s₁, b, s₂, rfl, hz⟩ := hz
    exact Shape.Subst.intTrap hz
  | there hz _ ih =>
    obtain ⟨a, args, s₁, b, s₂, rfl, hz⟩ := hz
    exact Shape.Subst.int hz ih

theorem substL_cases_aux {c : (wasmHShape H).ClosedMod} {e : End (wasmHShape H).S (List Val ⊕ Nat)}
    {L : List (HCall H)} {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (h : Shape.Subst c L e y) : ∀ l : List (OCall H), L = l.map OCall.lift →
      (∃ q, AllRetL c l q ∧ y = (q, e)) ∨ (∃ q, TrapAtL c l q ∧ y = (q, .trap)) ∨
        (y.2 = .div ∧ ∃ q₁ q₂ z, y.1 = q₁ ++ q₂ ∧ z ∈ l ∧ DivsL c z q₂) := by
  induction h with
  | nil e =>
    intro l hl
    cases l with
    | nil => exact .inl ⟨[], .nil, rfl⟩
    | cons z l => cases hl
  | ext _ ih =>
    intro l hl
    cases l with
    | nil => cases hl
    | cons z l =>
      obtain ⟨a, args, s₁, b, s₂, rfl⟩ := OCall.eq_mk z
      simp only [List.map_cons, lift_mk, List.cons.injEq] at hl
      obtain ⟨hz, -⟩ := hl
      cases hz
  | @int g a₀ s₀ b₀ s₀' rest e c₁ y hc _ ih =>
    intro l hl
    cases l with
    | nil => cases hl
    | cons z l =>
      obtain ⟨a, args, s₁, b, s₂, rfl⟩ := OCall.eq_mk z
      simp only [List.map_cons, lift_mk, List.cons.injEq] at hl
      obtain ⟨hz, hl⟩ := hl
      cases hz
      have hr : RetL c _ _ := ⟨_, _, _, _, _, rfl, hc⟩
      rcases ih l hl with ⟨q, h₁, e'⟩ | ⟨q, h₁, e'⟩ | ⟨hd, q₁, q₂, z, e', hz, h₁⟩
      · subst e'; exact .inl ⟨_, .cons hr h₁, rfl⟩
      · subst e'; exact .inr (.inl ⟨_, .there hr h₁, rfl⟩)
      · refine .inr (.inr ⟨hd, c₁ ++ q₁, q₂, z, ?_, List.mem_cons_of_mem _ hz, h₁⟩)
        simp [e']
  | intTrap hc =>
    intro l hl
    cases l with
    | nil => cases hl
    | cons z l =>
      obtain ⟨a, args, s₁, b, s₂, rfl⟩ := OCall.eq_mk z
      simp only [List.map_cons, lift_mk, List.cons.injEq] at hl
      obtain ⟨hz, -⟩ := hl
      cases hz
      exact .inr (.inl ⟨_, .here ⟨_, _, _, _, _, rfl, hc⟩, rfl⟩)
  | intDiv hc =>
    intro l hl
    cases l with
    | nil => cases hl
    | cons z l =>
      obtain ⟨a, args, s₁, b, s₂, rfl⟩ := OCall.eq_mk z
      simp only [List.map_cons, lift_mk, List.cons.injEq] at hl
      obtain ⟨hz, -⟩ := hl
      cases hz
      exact .inr (.inr ⟨rfl, [], _, _, rfl, List.mem_cons_self, _, _, _, _, _, rfl, hc⟩)

/-- **What resolving a lifted log can give.** -/
theorem substL_cases {c : (wasmHShape H).ClosedMod} {e : End (wasmHShape H).S (List Val ⊕ Nat)}
    {l : List (OCall H)} {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (h : Shape.Subst c (l.map OCall.lift) e y) :
    (∃ q, AllRetL c l q ∧ y = (q, e)) ∨ (∃ q, TrapAtL c l q ∧ y = (q, .trap)) ∨
      (y.2 = .div ∧ ∃ q₁ q₂ z, y.1 = q₁ ++ q₂ ∧ z ∈ l ∧ DivsL c z q₂) :=
  substL_cases_aux h l rfl

end Silmaril.Proofs.Wasm.Abstract.HostClosing
