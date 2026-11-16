module

public import Silmaril.Sim.X86.SumTo.Defs
public import Silmaril.Sim.X86.Loop.Thms

/-!
# `sum_to`: the Wasm problem, solved with the dispatcher's cut-point rule

`wasm_solution`: the Wasm problem of `sum_to` (`LProblem … (dispCode (compileTab (sumTab b)))`)
at every profile and for every host relation. The invariant (`PC`) names one assertion per cut
point (each address of the table, and the exit `b + 15`); `dispatch_hwp` reduces the loop to one
straight-line Wasm problem per entry, `step0` … `step13`, each evaluated by `simp` on the
generated code (`sum_step`). The arithmetic left: `tri_step` (one iteration of the sum).
-/

@[expose] public section

namespace Silmaril.Sim.X86.SumTo

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.X86 (Reg Word)
open Silmaril.Sim.X86.G Silmaril.Sim.X86.Loop
open Silmaril.Wasm.Logic.Core (exec exec_cons exec_nil)

variable {H : Type} {s : Store H} {f : Frame}

/-- The four globals `sum_to`'s code reads, with the layout. -/

def Vals (s : Store H) (f : Frame) (R : Reg → Word) (rip rax rdi zf : Word) : Prop :=
  Layout s f ∧ gval s f .rip = some (Val.i64 rip) ∧ gval s f (.reg .rax) = some (Val.i64 rax) ∧
    gval s f (.reg .rdi) = some (Val.i64 rdi) ∧ gval s f .zf = some (Val.i64 zf) ∧
    ∀ r, r ≠ .rax → r ≠ .rdi → gval s f (.reg r) = some (Val.i64 (R r))

theorem zf_val (r : Word) : 1 ^^^ (r ||| 0 - r) >>> 63 = b64 (r == 0) := by
  rw [shr63, msb_or_neg]; cases r == 0 <;> rfl

/-- Evaluate one entry of the dispatcher on a store given by `Vals`. -/
syntax "sum_step" : tactic
macro_rules
  | `(tactic| sum_step) => `(tactic| (
    simp (maxDischargeDepth := 20) (contextual := true) only [aluCode, carryCode, overflowCode, zeroCode, msbCode,
      notCode, aluWasm, nextCode, testCode, decCode, zero32Code, jccCode,
      List.cons_append, List.nil_append, exec_cons, exec_nil,
      exec1_gget, Layout.upd, Option.map_some, exec1_c64, exec1_add, exec1_sub,
      exec1_and, exec1_or, exec1_xor, exec1_shr63, exec1_gset, gval_upd, reduceCtorEq, ite_false,
      ite_true, Option.some.injEq, Prod.mk.injEq, and_true, exists_eq_left', Vals, true_and,
      Loc.reg.injEq, val_i64_inj, zf_val, BitVec.and_self, exists_eq', ne_eq, not_false_eq_true, implies_true, *] <;>
    first | rfl | exact ⟨rfl, zf_val _⟩ | exact ⟨_, rfl, rfl⟩))

theorem step0 {R : Reg → Word} {rip rax rdi zf : Word} (h : Vals s f R rip rax rdi zf) :
    ∃ s', exec s f [] (zero32Code .rax ++ nextCode 2) = some (s', f, []) ∧
      Vals s' f R (rip + 2) 0 rdi 1 := by
  obtain ⟨hl, h1, h2, h3, h4, h5⟩ := h
  sum_step
theorem step2 {R : Reg → Word} {rip rax rdi zf : Word} (h : Vals s f R rip rax rdi zf) :
    ∃ s', exec s f [] (testCode .rdi .rdi ++ nextCode 3) = some (s', f, []) ∧
      Vals s' f R (rip + 3) rax rdi (b64 (rdi == 0)) := by
  obtain ⟨hl, h1, h2, h3, h4, h5⟩ := h
  sum_step
theorem step5 {R : Reg → Word} {rip rax rdi zf : Word} (h : Vals s f R rip rax rdi zf) :
    ∃ s', exec s f [] (jccCode [gget .zf] 8 2) = some (s', f, []) ∧
      Vals s' f R (rip + 2 + ((0 - zf) &&& 8)) rax rdi zf := by
  obtain ⟨hl, h1, h2, h3, h4, h5⟩ := h
  sum_step
theorem step7 {R : Reg → Word} {rip rax rdi zf : Word} (h : Vals s f R rip rax rdi zf) :
    ∃ s', exec s f [] (aluCode .add .rax .rdi ++ nextCode 3) = some (s', f, []) ∧
      ∃ zf', Vals s' f R (rip + 3) (rax + rdi) rdi zf' := by
  obtain ⟨hl, h1, h2, h3, h4, h5⟩ := h
  sum_step
theorem step10 {R : Reg → Word} {rip rax rdi zf : Word} (h : Vals s f R rip rax rdi zf) :
    ∃ s', exec s f [] (decCode .rdi ++ nextCode 3) = some (s', f, []) ∧
      Vals s' f R (rip + 3) rax (rdi - 1) (b64 (rdi - 1 == 0)) := by
  obtain ⟨hl, h1, h2, h3, h4, h5⟩ := h
  sum_step
theorem step13 {R : Reg → Word} {rip rax rdi zf : Word} (h : Vals s f R rip rax rdi zf) :
    ∃ s', exec s f [] (jccCode [gget .zf, c64 1, b64op .xor] 0xf8 2) = some (s', f, []) ∧
      Vals s' f R (rip + 2 + ((0 - (zf ^^^ 1)) &&& 0xfffffffffffffff8)) rax rdi zf := by
  obtain ⟨hl, h1, h2, h3, h4, h5⟩ := h
  sum_step

theorem tri_mono {k m : Nat} (h : k ≤ m) : tri k ≤ tri m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => simp only [tri]; omega

theorem tri_step (k N : Word) (hk : k ≠ 0) (hle : k.toNat ≤ N.toNat) :
    BitVec.ofNat 64 (tri N.toNat - tri k.toNat) + k =
      BitVec.ofNat 64 (tri N.toNat - tri (k - 1).toNat) := by
  have hk0 : k.toNat ≠ 0 := fun e => hk (BitVec.eq_of_toNat_eq (by simpa using e))
  have h1 : (k - 1).toNat = k.toNat - 1 := by bv_omega
  obtain ⟨K, hK⟩ : ∃ K, k.toNat = K + 1 := ⟨k.toNat - 1, by omega⟩
  have hm := tri_mono hle
  rw [h1, hK, Nat.add_sub_cancel]
  rw [hK] at hm
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hK]
  simp only [tri] at hm ⊢
  rw [Nat.mod_add_mod]
  congr 1
  omega

theorem b64_xor_one (t : Bool) : b64 t ^^^ 1 = b64 (!t) := by cases t <;> decide

/-- The cut points of `sum_to` at `b` with initial `rdi = N`. -/
def PC (N b rip rax rdi zf : Word) : Prop :=
  (rip = b ∧ rdi = N) ∨
  (rip = b + 2 ∧ rdi = N ∧ rax = 0) ∨
  (rip = b + 5 ∧ rdi = N ∧ rax = 0 ∧ zf = b64 (N == 0)) ∨
  (rip = b + 7 ∧ rdi ≠ 0 ∧ rdi.toNat ≤ N.toNat ∧
    rax = BitVec.ofNat 64 (tri N.toNat - tri rdi.toNat)) ∨
  (rip = b + 10 ∧ rdi ≠ 0 ∧ rdi.toNat ≤ N.toNat ∧
    rax = BitVec.ofNat 64 (tri N.toNat - tri rdi.toNat) + rdi) ∨
  (rip = b + 13 ∧ rdi.toNat < N.toNat ∧ rax = BitVec.ofNat 64 (tri N.toNat - tri rdi.toNat) ∧
    zf = b64 (rdi == 0)) ∨
  (rip = b + 15 ∧ rax = BitVec.ofNat 64 (tri N.toNat))

theorem ctab_eq (b : Word) : compileTab (sumTab b) =
    [(b, zero32Code .rax ++ nextCode 2), (b + 2, testCode .rdi .rdi ++ nextCode 3),
     (b + 5, jccCode [gget .zf] 8 2), (b + 7, aluCode .add .rax .rdi ++ nextCode 3),
     (b + 10, decCode .rdi ++ nextCode 3),
     (b + 13, jccCode [gget .zf, c64 1, b64op .xor] 0xf8 2)] := rfl

variable {P : Profile} {host : HostSemantics H}

/-- **The Wasm problem of `sum_to` is solved.** -/
theorem wasm_solution (b : Word) :
    LProblem (H := H) P host (dispCode (compileTab (sumTab b))) (fun _ w => w = b) SumPost := by
  intro s f R w hG hw hb
  obtain ⟨hl, hr, -, -, ⟨bz, hz⟩, -, -⟩ := hG
  subst hb
  refine dispatch_hwp _ (fun s' => ∃ rip rax rdi zf, Vals s' f R rip rax rdi zf ∧
    PC (R .rdi) w rip rax rdi zf) _ ?_ ⟨w, R .rax, R .rdi, b64 bz,
      ⟨hl, hw, hr _, hr _, hz, fun r _ _ => hr r⟩, .inl ⟨rfl, rfl⟩⟩
  rintro s' ⟨rip, rax, rdi, zf, hV, hpc⟩
  refine ⟨rip, hV.2.1, ?_⟩
  rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hk, hle, rfl⟩ |
    ⟨rfl, hk, hle, rfl⟩ | ⟨rfl, hlt, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [ctab_eq, lookupC, ite_true]
    obtain ⟨s'', he, hV'⟩ := step0 hV
    exact ⟨s'', he, _, _, _, _, hV', .inr (.inl ⟨rfl, rfl, rfl⟩)⟩
  · simp [ctab_eq, lookupC]
    obtain ⟨s'', he, hV'⟩ := step2 hV
    refine ⟨s'', he, _, _, _, _, hV', .inr (.inr (.inl ⟨?_, rfl, rfl, rfl⟩))⟩
    simp [BitVec.add_assoc]
  · simp [ctab_eq, lookupC]
    obtain ⟨s'', he, hV'⟩ := step5 hV
    refine ⟨s'', he, _, _, _, _, hV', ?_⟩
    rw [jcc_bits]
    cases hN : (R .rdi == 0)
    · refine .inr (.inr (.inr (.inl ⟨?_, by simpa using hN, le_rfl, by simp⟩)))
      simp [BitVec.add_assoc]
    · have h0 : R .rdi = 0 := by simpa using hN
      refine .inr (.inr (.inr (.inr (.inr (.inr ⟨?_, by simp [h0, tri]⟩)))))
      simp [BitVec.add_assoc]
  · simp [ctab_eq, lookupC]
    obtain ⟨s'', he, zf', hV'⟩ := step7 hV
    refine ⟨s'', he, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inl ⟨?_, hk, hle, rfl⟩))))⟩
    simp [BitVec.add_assoc]
  · simp [ctab_eq, lookupC]
    obtain ⟨s'', he, hV'⟩ := step10 hV
    refine ⟨s'', he, _, _, _, _, hV', .inr (.inr (.inr (.inr (.inr (.inl
      ⟨?_, by bv_omega, tri_step _ _ hk hle, rfl⟩)))))⟩
    simp [BitVec.add_assoc]
  · simp [ctab_eq, lookupC]
    obtain ⟨s'', he, hV'⟩ := step13 hV
    refine ⟨s'', he, _, _, _, _, hV', ?_⟩
    rw [b64_xor_one, show (0xfffffffffffffff8 : Word) = 0xfffffffffffffff8 from rfl, jcc_bits]
    cases hN : (rdi == 0)
    · refine .inr (.inr (.inr (.inl ⟨?_, by simpa using hN, by omega, rfl⟩)))
      simp [BitVec.add_assoc]
    · have : rdi = 0 := by simpa using hN
      subst this
      refine .inr (.inr (.inr (.inr (.inr (.inr ⟨?_, by simp [tri]⟩)))))
      simp [BitVec.add_assoc]
  · simp [ctab_eq, lookupC]
    intro R' w' hR' hw'
    have h := hR' .rax
    rw [hV.2.2.1, Option.some.injEq, val_i64_inj] at h
    rw [hV.2.1, Option.some.injEq, val_i64_inj] at hw'
    refine ⟨h.symm, fun r h1 h2 => ?_, hw'.symm⟩
    have h' := hR' r
    rw [hV.2.2.2.2.2 r h1 h2, Option.some.injEq, val_i64_inj] at h'
    exact h'.symm

end Silmaril.Sim.X86.SumTo
