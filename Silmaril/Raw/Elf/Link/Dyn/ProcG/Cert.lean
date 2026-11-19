module

public import Silmaril.Elf.Link.Dyn.ProcG.Thms
public import Silmaril.Elf.Link.Dyn.Cert.Thms

/-! # Block certificates on the extended process machine

`Cert.must_blkX_at` steps a checked block certificate (`Cert.BlkX`) on `Proc.proc`. The same
certificate steps `procG L W` for any image machine `J` extending `Open9`: every instruction of
the listing is an `Open9` instruction of the view (`ProcG.mustG_insn`), and `L.put` keeps the rest
of the `J` state (for instance vector registers) across the whole block.

PROVED (standard axioms): `mustG_seqX`, `mustG_blkX`, **`mustG_blkX_at`** (the statement of
`Cert.must_blkX_at` with the final state `L.put x (post …)`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.ProcG

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.X86.Bir9 (Block Stmt Env XResult Xmm liftR)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded)
open Silmaril.X86.SegVC (Isa)
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Cert
open Silmaril.X86.Bir9X (XL toX9X liftBlockX execBlockX)

variable {τ : Type} {J : Isa τ}

/-- What a listing run on `procG` must lead to (from the `J` state `x`). -/
def XPostG (L : Silmaril.X86.Open9.isa.Extends J) (W : World) (Q : GState τ → Prop) (x : τ)
    (g : Ghost) : XResult → Prop
  | .ok t m => MustG L W Q ⟨L.put x ⟨t.core, m⟩, g⟩
  | _ => False

set_option maxHeartbeats 400000 in
/-- **A checked `Bir9X` listing runs on `procG`.** -/
theorem mustG_seqX (L : Silmaril.X86.Open9.isa.Extends J) {W : World} {Q : GState τ → Prop}
    {base : Word} {code : List Byte} :
    ∀ (Ls : List (XL × Nat)) (o : Nat) (x : τ) (g : Ghost) (v : Xmm),
    seqAtX code o Ls = true → g.done = none →
    (∀ o', o ≤ o' → o' < o + lenLX Ls → W.InImage (base + BitVec.ofNat 64 o').toNat) →
    Loaded (L.view x).memory base code → CodeRO (L.view x).memory base code →
    (Ls ≠ [] → (L.view x).core.rip = base + BitVec.ofNat 64 o) →
    XPostG L W Q x g (execBlockX Ls ⟨(L.view x).core, v⟩ (L.view x).memory) → MustG L W Q ⟨x, g⟩
  | [], _, x, g, v, _, _, _, _, _, _, h => by
    simp only [execBlockX, XPostG] at h
    rw [show (⟨(L.view x).core, (L.view x).memory⟩ : MState) = L.view x from rfl, L.put_view] at h
    exact h
  | (i, l) :: rest, o, x, g, v, hok, hd, hin, hl, hro, hrip, h => by
    simp only [seqAtX] at hok
    split at hok
    · cases hok
    · rename_i j hj
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨⟨⟨hdec, hl0⟩, hfit⟩, hft⟩, hlift⟩, hrest⟩ := hok
      have hrip' := hrip (List.cons_ne_nil _ _)
      have hx := xl_exec hj v (L.view x).core (L.view x).memory l
      obtain ⟨c, m', he⟩ : ∃ c m', Silmaril.X86.Ext9.exec j (L.view x).core (L.view x).memory l = .ok c m' := by
        revert h
        simp only [execBlockX, hx]
        cases Silmaril.X86.Ext9.exec j (L.view x).core (L.view x).memory l <;> simp [liftR, XPostG]
      have hx' : i.exec ⟨(L.view x).core, v⟩ (L.view x).memory l = .ok ⟨c, v⟩ m' := by rw [hx, he]; rfl
      have hb : execBlockX ((i, l) :: rest) ⟨(L.view x).core, v⟩ (L.view x).memory =
          execBlockX rest ⟨c, v⟩ m' := by
        simp only [execBlockX, hx']
      rw [hb] at h
      obtain ⟨bi, hbi⟩ := Option.isSome_iff_exists.mp hlift
      have hfr : Frame (L.view x).memory m' := by
        have h1 := Silmaril.X86.Bir9X.liftBlockX_sound hbi ⟨(L.view x).core, v⟩ (L.view x).memory
        have h2 : execBlockX [(i, l)] ⟨(L.view x).core, v⟩ (L.view x).memory = .ok ⟨c, v⟩ m' := by
          simp only [execBlockX, hx']
        rw [h2] at h1
        exact block_frame h1.symm
      refine mustG_insn L hd (by rw [hrip']; exact hin o (Nat.le_refl _) (by simp only [lenLX]; omega))
        hl hrip' hfit hdec ?_
      rw [he, WP_ok]
      have hv : L.view (L.put x ⟨c, m'⟩) = ⟨c, m'⟩ := L.view_put _ _
      refine mustG_seqX L rest (o + l) (L.put x ⟨c, m'⟩) g v hrest hd
        (fun o' h1 h2 => hin o' (by omega) (by simp only [lenLX]; omega))
        (by rw [hv]; exact loaded_frame hl hro hfr) (by rw [hv]; exact codeRO_frame hro hfr)
        (fun hne => ?_) ?_
      · have hf : Silmaril.X86.BlockCert9.fallsThrough9 j = true := by
          cases rest with
          | nil => exact absurd rfl hne
          | cons _ _ => simpa using hft
        rw [hv]
        show c.rip = _
        rw [exec_rip9 hf he, hrip', ripadd]
      · rw [hv]
        revert h
        cases execBlockX rest ⟨c, v⟩ m' with
        | ok t mm => simp only [XPostG, L.put_put]; exact id
        | _ => simp [XPostG]

/-- **The checker lemma for `BlkX` on `procG`.** -/
theorem mustG_blkX (L : Silmaril.X86.Open9.isa.Extends J) {W : World} {Q : GState τ → Prop}
    {s : GState τ} {base : Word} {code : List Byte}
    (B : BlkX) (hok : B.ok code = true) (hd : s.g.done = none)
    (hin : ∀ o', B.off ≤ o' → o' < B.off + B.len → W.InImage (base + BitVec.ofNat 64 o').toNat)
    (hl : Loaded (L.view s.x).memory base code) (hro : CodeRO (L.view s.x).memory base code)
    (hrip : (L.view s.x).core.rip = base + BitVec.ofNat 64 B.off)
    (h : Wp B.b.stmts (env0 (L.view s.x)) fun env =>
      MustG L W Q ⟨L.put s.x (post B.b ⟨L.view s.x, s.g⟩ env).m, s.g⟩) : MustG L W Q s := by
  simp only [BlkX.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hseq, hlift⟩ := hok
  refine mustG_seqX L B.L B.off s.x s.g (fun _ => 0) hseq hd hin hl hro (fun _ => hrip) ?_
  rw [Silmaril.X86.Bir9X.liftBlockX_sound hlift]
  obtain ⟨env, he, hP⟩ := (wp_iff _ _ _).1 h
  unfold Block.run
  simp only [env0] at he
  rw [he]
  exact hP

/-- **`mustG_blkX` for a chunk in the image** (as `Cert.must_blkX_at`). -/
theorem mustG_blkX_at (L : Silmaril.X86.Open9.isa.Extends J) {W : World} {Q : GState τ → Prop}
    {s : GState τ} {b : Word} {cb : Nat}
    {code : List Byte} (B : BlkX) (hok : B.ok code = true) (hd : s.g.done = none)
    (himg : ∀ n, n < code.length → W.InImage (b + BitVec.ofNat 64 (cb + n)).toNat)
    (hl : Loaded (L.view s.x).memory (b + BitVec.ofNat 64 cb) code)
    (hro : CodeRO (L.view s.x).memory (b + BitVec.ofNat 64 cb) code)
    (hrip : (L.view s.x).core.rip = b + BitVec.ofNat 64 (cb + B.off))
    (h : Wp B.b.stmts (env0 (L.view s.x)) fun env =>
      MustG L W Q ⟨L.put s.x (post B.b ⟨L.view s.x, s.g⟩ env).m, s.g⟩) : MustG L W Q s := by
  have hfit : B.off + B.len ≤ code.length ∨ B.L = [] := by
    simp only [BlkX.ok, Bool.and_eq_true] at hok; exact seqAtX_fit _ _ hok.1
  refine mustG_blkX L B hok hd (fun o' h1 h2 => ?_) hl hro (by rw [hrip, ripadd]) h
  rw [ripadd]
  rcases hfit with hf | hn
  · exact himg o' (by omega)
  · simp [BlkX.len, hn, lenLX] at h2; omega

end Silmaril.Elf.Link.Dyn.ProcG
