module

public import Silmaril.Proofs.Wasm.Examples.LratAccept.Cert

@[expose] public section

/-!
# The reset of the LRAT state

`reset_hwp`: from **any** LRAT view `Shape X s G B`, every run of `resetCode` (zero the words of
memory `0` below the arena, give the eight globals their initial values `G₀`) reaches a view
`Shape X s' G₀ B'` with `Good [] G₀ B'`: the state of a fresh instance for the empty stream
(`good_reset`). So the checks need no assumption on the LRAT state they start from.

Every profile and host relation. A Silmaril addition.
-/

namespace Silmaril.Proofs.Wasm.Examples.LratAccept

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Examples.LRAT
open Silmaril.Wasm.Examples.LratAccept

variable {H : Type} {P : Profile} {host : HostSemantics H} {X : Fix H}

theorem litAddr_dvd (x : BitVec 32) : 4 ∣ litAddr x := by
  unfold litAddr; bv_omega

/-- **The reset state is good**: a memory of the right size whose words below the arena are `0`,
with the initial globals, satisfies the invariant for the empty stream. -/
theorem good_reset {B : ByteArray} (hsz : B.size = memSize)
    (hz : ∀ a, 4 ∣ a → a < arenaBase → wd B a = 0#32) : Good [] G₀ B := by
  have hlen : ∀ id < maxId, entryLen B id = 0 := by
    intro id hid
    simp only [entryLen]
    rw [hz _ (by simp only [lenBase]; omega) (by simp only [lenBase, maxId, arenaBase] at *; omega)]
    rfl
  have hmod : ∀ τ, Models τ B := fun τ =>
    models_iff.2 fun id hid hl => absurd (hlen id hid) hl
  have hbuf : bufWords G₀ B = [] := rfl
  exact {
    size := hsz
    mode_le := by decide
    base_le := by decide
    cstart_le := by decide
    top_le := by decide
    cstart_dvd := by decide
    top_dvd := by decide
    stamp_le := by decide
    stale := fun x hx => by
      have ha := hx.addr
      rw [hz _ (litAddr_dvd x) (by simp only [startBase, arenaBase] at *; omega)]
      simp
    tag_le := by
      simp only [tagOf]
      rw [hz _ (by decide) (by decide)]
      simp
    cov_le := fun id hid => by
      simp only [covOf, tagOf]
      rw [hz _ (by simp only [covBase]; omega) (by simp only [covBase, maxId, arenaBase] at *; omega),
        hz _ (by decide) (by decide)]
    entries := fun id hid hl => absurd (hlen id hid) hl
    sat := fun _ => ⟨fun _ => true, hmod _⟩
    unsat := fun h => absurd rfl h
    input := fun _ => by
      rw [hbuf]; exact ⟨fun _ h => absurd h List.not_mem_nil, rfl, fun τ _ => hmod τ⟩
    step := fun h => absurd h (by decide) }

/-- The zeroing loop's invariant. -/
def ZInv (X : Fix H) (G : List (BitVec 32)) (pp pl cp cl l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : BitVec 32) :
    Store H → Frame → Prop := fun s f =>
  ∃ (B : ByteArray) (i : BitVec 32), Shape X s G B ∧
    f = fr X.mi [pp, pl, cp, cl, i, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15] ∧
    i.toNat ≤ arenaBase ∧ 4 ∣ i.toNat ∧ ∀ a, 4 ∣ a → a < i.toNat → wd B a = 0#32

variable {s : Store H} {G : List (BitVec 32)} {B : ByteArray}

set_option maxHeartbeats 4000000 in
set_option linter.unusedTactic false in
/-- **The reset**, from any LRAT view. -/
theorem reset_hwp (hX : MiOk X) (hS : Shape X s G B)
    {pp pl cp cl l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 : BitVec 32} {rest : List Admin}
    {Q : Post H}
    (k : ∀ s' B', Shape X s' G₀ B' → Good [] G₀ B' →
      HWP P host s' (fr X.mi [pp, pl, cp, cl, 24576#32, l5, l6, l7, l8, l9, l10, l11, l12, l13,
        l14, l15]) (vals ([] : List Val).reverse ++ rest) Q) :
    HWP P host s (fr X.mi [pp, pl, cp, cl, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15])
      (vals ([] : List Val).reverse ++ expression resetCode ++ rest) Q := by
  obtain ⟨m, t, c, S, cf, sid, u, n, rfl⟩ := G_eight hS.len
  simp only [resetCode, expression, List.map_cons, List.map_nil, List.cons_append,
    List.append_assoc]
  refine w_const ?_
  refine w_lset (by simp) (by decide) ?_
  simp only [List.set_cons_succ, List.set_cons_zero]
  refine w_while (Inv := ZInv X _ pp pl cp cl l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15)
    ⟨B, 0#32, hS, rfl, by simp [arenaBase], by simp, fun a _ ha => absurd ha (by simp)⟩ ?_
  rintro s f ⟨B, i, hS, rfl, hi, hd, hz⟩
  simp only [zeroLoopBody, expression, List.map_cons, List.map_nil]
  wstep; try wnorm
  wstep; try wnorm
  wstep; try wnorm
  refine w_brIf (fun hx => ?_) (fun hx => ?_)
  · have hi' : i.toNat = arenaBase := by
      have := b32_ne_zero.1 hx; simp only [arenaBase] at *; omega
    refine w_br (whilePost_exit ?_)
    wrun
    have hieq : i = 24576#32 := BitVec.eq_of_toNat_eq (by simp [hi', arenaBase])
    subst hieq
    rw [List.nil_append]
    exact k _ B (by assumption) (good_reset hS.size fun a ha hlt => hz a ha (by omega))
  · have hlt : i.toNat < arenaBase := by
      have := b32_eq_zero.1 hx; simp only [arenaBase] at *; omega
    wstep; try wnorm
    wstep; try wnorm
    refine w_store hS hX (by simp only [memSize, arenaBase] at *; omega) fun s' hS' => ?_
    wstep; try wnorm
    wstep; try wnorm
    wstep; try wnorm
    wstep; try wnorm
    have hi4 : (i + 4#32).toNat = i.toNat + 4 := by
      simp only [arenaBase] at hlt; bv_omega
    refine w_br (whilePost_cont ⟨_, i + 4#32, hS', rfl, by rw [hi4]; simp only [arenaBase] at *; omega,
      by rw [hi4]; omega, fun a ha hlt' => ?_⟩)
    rw [hi4] at hlt'
    by_cases hai : a = i.toNat
    · subst hai
      exact wd_wr_same _ (by rw [hS.size]; simp only [memSize, arenaBase] at *; omega)
    · rw [wd_wr_ne _ (by rw [hS.size]; simp only [memSize, arenaBase] at *; omega) (by omega)]
      exact hz a ha (by omega)

end Silmaril.Proofs.Wasm.Examples.LratAccept
