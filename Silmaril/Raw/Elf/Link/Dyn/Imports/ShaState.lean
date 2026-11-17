module

public import Silmaril.Elf.Link.Dyn.Imports.Defs

/-! # SHA-256 has a finite streaming state

`Sig m` (the SHA-256 state after the full 64-byte blocks of `m`, the remaining bytes, and the
bit length modulo `2^64`) is what a `SHA256_CTX` must hold: it is updated by appending
(`sig_append`) and determines the digest (`digest_eq_of_sig`). `enc` writes it in 112 bytes and
`dec` reads it back (`dec_enc`). This is the mathematical half of the non-vacuity of the
`SHA256_*` contracts (`ShaRep`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Imports.ShaState

open Silmaril.Crypto Silmaril.Crypto.SHA256
open Silmaril.X86 (Byte)

/-- The full 64-byte blocks of `p`, absorbed into `st` (as `hash` does). -/
def absorb (st : State) (p : List UInt8) : State :=
  (List.range (p.length / 64)).foldl (fun st i =>
    processBlock st (parseBlock ((p.drop (64 * i)).take 64))) st

theorem hash_eq (msg : List UInt8) : SHA256.hash msg = absorb H0 (paddingMD msg) := rfl

private theorem foldl_congr {α β : Type} {f g : β → α → β} :
    ∀ (l : List α), (∀ x ∈ l, ∀ b, f b x = g b x) → ∀ b, l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | x :: l, h, b => by
    simp only [List.foldl_cons]
    rw [h x (by simp) b]
    exact foldl_congr l (fun y hy => h y (by simp [hy])) _

theorem absorb_append (st : State) (a b : List UInt8) (ha : 64 ∣ a.length) :
    absorb st (a ++ b) = absorb (absorb st a) b := by
  obtain ⟨q, hq⟩ := ha
  have hl : (a ++ b).length / 64 = q + b.length / 64 := by simp [hq]; omega
  unfold absorb
  rw [hl, List.range_add, List.foldl_append, List.foldl_map, hq, Nat.mul_div_cancel_left _ (by decide)]
  rw [foldl_congr (List.range q) (g := fun st i => processBlock st (parseBlock ((a.drop (64 * i)).take 64)))]
  · apply foldl_congr
    intro j _ s
    have : 64 * (q + j) = a.length + 64 * j := by rw [hq]; omega
    rw [this, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
    congr 4
    simp
  · intro i hi s
    simp only [List.mem_range] at hi
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

/-- What a context holds after absorbing `m`. -/
structure Sig where
  H : State
  t : List UInt8
  L : Nat

def full (m : List UInt8) : List UInt8 := m.take (64 * (m.length / 64))
def rest (m : List UInt8) : List UInt8 := m.drop (64 * (m.length / 64))

def sig (m : List UInt8) : Sig := ⟨absorb H0 (full m), rest m, m.length * 8 % 2 ^ 64⟩

def Sig.step (σ : Sig) (d : List UInt8) : Sig :=
  ⟨absorb σ.H (full (σ.t ++ d)), rest (σ.t ++ d), (σ.L + d.length * 8) % 2 ^ 64⟩

/-- The final blocks. -/
def Sig.pad (σ : Sig) : List UInt8 :=
  σ.t ++ [padFirstByte] ++ List.replicate (paddingZeroCount σ.t.length) padZero ++ natToBytesBE64 σ.L

theorem full_length (m : List UInt8) : (full m).length = 64 * (m.length / 64) := by
  simp only [full, List.length_take]; omega

theorem rest_length (m : List UInt8) : (rest m).length = m.length % 64 := by
  simp only [rest, List.length_drop]; omega

theorem full_rest (m : List UInt8) : full m ++ rest m = m := List.take_append_drop _ _

theorem sig_append (m d : List UInt8) : sig (m ++ d) = (sig m).step d := by
  have hsplit : m ++ d = full m ++ (rest m ++ d) := by rw [← List.append_assoc, full_rest]
  have hF := full_length m
  have hR := rest_length m
  have hq : (m ++ d).length / 64 = m.length / 64 + (rest m ++ d).length / 64 := by
    rw [List.length_append, List.length_append, hR]; omega
  have e1 : full (m ++ d) = full m ++ full (rest m ++ d) := by
    rw [show full (m ++ d) = (m ++ d).take (64 * ((m ++ d).length / 64)) from rfl, hq, hsplit,
      List.take_append, List.take_of_length_le (by rw [hF]; omega), hF]
    show _ = _ ++ (rest m ++ d).take (64 * ((rest m ++ d).length / 64))
    congr 2; omega
  have e2 : rest (m ++ d) = rest (rest m ++ d) := by
    rw [show rest (m ++ d) = (m ++ d).drop (64 * ((m ++ d).length / 64)) from rfl, hq, hsplit,
      List.drop_append, List.drop_eq_nil_of_le (by rw [hF]; omega), List.nil_append, hF]
    show _ = (rest m ++ d).drop (64 * ((rest m ++ d).length / 64))
    congr 1; omega
  simp only [sig, Sig.step, Sig.mk.injEq]
  refine ⟨?_, e2, ?_⟩
  · rw [e1, absorb_append _ _ _ ⟨_, hF⟩]
  · simp only [List.length_append]; omega

theorem hash_sig (m : List UInt8) : SHA256.hash m = absorb (sig m).H (sig m).pad := by
  show absorb H0 (paddingMD m) = absorb (absorb H0 (full m)) (sig m).pad
  rw [← absorb_append _ _ _ ⟨_, full_length m⟩]
  congr 1
  have hR := rest_length m
  have hz : paddingZeroCount m.length = paddingZeroCount (rest m).length := by
    simp only [paddingZeroCount, hR, Nat.mod_mod]
  have hn : natToBytesBE64 (m.length * 8) = natToBytesBE64 (m.length * 8 % 2 ^ 64) := by
    simp only [natToBytesBE64, Nat.mod_mod]
  simp only [paddingMD, sig, Sig.pad, hz, hn, List.append_assoc]
  rw [← List.append_assoc (full m), full_rest]

theorem digest_eq_of_sig {m1 m2 : List UInt8} (h : sig m1 = sig m2) : digest m1 = digest m2 := by
  have : SHA256.hash m1 = SHA256.hash m2 := by rw [hash_sig, hash_sig m2, h]
  simp only [digest, this]

/-! ## 112 bytes -/

def hw (x : UInt32) : List Byte :=
  [(toBytesBE32 x).1.toBitVec, (toBytesBE32 x).2.1.toBitVec, (toBytesBE32 x).2.2.1.toBitVec,
   (toBytesBE32 x).2.2.2.toBitVec]

def encH : State → List Byte
  | (a, b, c, d, e, f, g, h) => hw a ++ hw b ++ hw c ++ hw d ++ hw e ++ hw f ++ hw g ++ hw h

def decW (l : List Byte) (i : Nat) : UInt32 :=
  ofBytesBE32 (UInt8.ofBitVec (l.getD i 0)) (UInt8.ofBitVec (l.getD (i + 1) 0))
    (UInt8.ofBitVec (l.getD (i + 2) 0)) (UInt8.ofBitVec (l.getD (i + 3) 0))

def decH (l : List Byte) : State :=
  (decW l 0, decW l 4, decW l 8, decW l 12, decW l 16, decW l 20, decW l 24, decW l 28)

def enc (σ : Sig) : List Byte :=
  encH σ.H ++ BitVec.ofNat 8 σ.t.length :: (σ.t.map UInt8.toBitVec ++
    (List.replicate (64 - σ.t.length) 0 ++ (Silmaril.X86.Ext.leBytes (BitVec.ofNat 64 σ.L) 8 ++
    List.replicate 7 0)))

def dec (l : List Byte) : Sig :=
  ⟨decH l, ((l.drop 33).take (l.getD 32 0).toNat).map UInt8.ofBitVec,
   Silmaril.X86.Ext.leValue ((l.drop 97).take 8)⟩

theorem encH_length (H : State) : (encH H).length = 32 := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := H; rfl

theorem decW_hw (x : UInt32) (r : List Byte) : decW (hw x ++ r) 0 = x := by
  simp only [decW, hw, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, UInt8.ofBitVec_toBitVec]
  exact ofBytesBE32_toBytesBE32 x

theorem decH_encH (H : State) (r : List Byte) : decH (encH H ++ r) = H := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := H
  have k : ∀ (x : UInt32) (p : List Byte) (r : List Byte) (i : Nat), p.length = i →
      decW (p ++ (hw x ++ r)) i = x := by
    intro x p r i hp
    subst hp
    have : ∀ j, (p ++ (hw x ++ r)).getD (p.length + j) 0 = (hw x ++ r).getD j 0 := by
      intro j; simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
    have h0 := this 0
    rw [Nat.add_zero] at h0
    unfold decW
    rw [h0, this 1, this 2, this 3]
    exact decW_hw x r
  simp only [encH, List.append_assoc, decH]
  simp only [Prod.mk.injEq]
  refine ⟨k a [] _ 0 rfl, k b (hw a) _ 4 rfl, k c (hw a ++ hw b) _ 8 rfl,
    k d (hw a ++ hw b ++ hw c) _ 12 rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [← List.append_assoc]
  · exact k e (hw a ++ hw b ++ hw c ++ hw d) _ 16 rfl
  · exact k f (hw a ++ hw b ++ hw c ++ hw d ++ hw e) _ 20 rfl
  · exact k g (hw a ++ hw b ++ hw c ++ hw d ++ hw e ++ hw f) _ 24 rfl
  · exact k h (hw a ++ hw b ++ hw c ++ hw d ++ hw e ++ hw f ++ hw g) _ 28 rfl

/-- A state reachable by absorbing. -/
def Sig.Ok (σ : Sig) : Prop := σ.t.length < 64 ∧ σ.L < 2 ^ 64

theorem sig_ok (m : List UInt8) : (sig m).Ok := by
  refine ⟨?_, Nat.mod_lt _ (by decide)⟩
  show (rest m).length < 64
  rw [rest_length]; omega

theorem enc_length (σ : Sig) (h : σ.Ok) : (enc σ).length = 112 := by
  simp only [enc, List.length_append, encH_length, List.length_cons, List.length_map,
    List.length_replicate, Silmaril.X86.Ext.length_leBytes]
  have := h.1; omega

theorem getD_32 (H : State) (x : Byte) (r : List Byte) : (encH H ++ x :: r).getD 32 0 = x := by
  simp [List.getD_eq_getElem?_getD, encH_length]

theorem drop_33 (H : State) (x : Byte) (r : List Byte) (k : Nat) :
    (encH H ++ x :: r).drop (33 + k) = r.drop k := by
  rw [show 33 + k = (encH H).length + (k + 1) by rw [encH_length]; omega, List.drop_length_add_append]
  rfl

theorem dec_enc (σ : Sig) (h : σ.Ok) : dec (enc σ) = σ := by
  obtain ⟨H, t, L⟩ := σ
  obtain ⟨ht, hL⟩ := h
  simp only at ht hL
  simp only [dec, enc, Sig.mk.injEq]
  refine ⟨decH_encH _ _, ?_, ?_⟩
  · rw [getD_32, ← Nat.add_zero 33, drop_33, List.drop_zero, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]
    simp [Function.comp_def]
  · rw [show 97 = 33 + ((t.map UInt8.toBitVec).length + (64 - t.length)) by simp; omega, drop_33,
      List.drop_append, List.drop_eq_nil_of_le (by simp), List.nil_append, Nat.add_sub_cancel_left,
      List.drop_left' (by simp), List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp), Silmaril.X86.Ext.leValue_leBytes, BitVec.toNat_ofNat,
      Nat.mod_mod_of_dvd _ (by decide), Nat.mod_eq_of_lt hL]

theorem step_ok (m d : List UInt8) : ((sig m).step d).Ok := by
  rw [← sig_append]; exact sig_ok _

end Silmaril.Elf.Link.Dyn.Imports.ShaState
