module

public import Silmaril.Raw.Elf.Link.Dyn.Imports.ShaState
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Progress

/-! # The `SHA256_*` contracts are satisfiable

`shaRep`: a context holds `m` when its 112 bytes decode (`ShaState.dec`) to the streaming state
`ShaState.sig m`. With it, every one of `sha256InitStep`, `sha256UpdateStep` and
`sha256FinalStep` has an outcome from every state (`sha_contracts_satisfiable`): an
implementation exists, so the conditional statements over these contracts are not vacuous.
(OpenSSL's real layout differs; the contracts do not mention it.)
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Imports

open Silmaril.X86 (Word Byte)
open Silmaril.Process (Memory Access)
open Silmaril.Elf.Link.Dyn.Proc
open ShaState

/-- The context at `ctx` holds the 112 bytes `bs` (whatever the permissions). -/
def CtxBytes (m : Memory) (ctx : Word) (bs : List Byte) : Prop :=
  bs.length = 112 ∧ ∀ i, i < 112 → m.bytes.get? (ctx.toNat + i) = bs[i]?

def shaRep : ShaRep where
  holds m ctx msg := ∃ bs, CtxBytes m ctx bs ∧ dec bs = sig (msg.map UInt8.ofBitVec)
  local_ := by
    rintro m m' ctx msg hk ⟨bs, ⟨hl, hb⟩, hd⟩
    refine ⟨bs, ⟨hl, fun i hi => ?_⟩, hd⟩
    rw [(hk _ ⟨by omega, by omega⟩).1, hb i hi]

theorem ctxBytes_unique {m : Memory} {ctx : Word} {b1 b2 : List Byte} (h1 : CtxBytes m ctx b1)
    (h2 : CtxBytes m ctx b2) : b1 = b2 := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 112
  · rw [← h1.2 i hi, h2.2 i hi]
  · rw [List.getElem?_eq_none (by rw [h1.1]; omega), List.getElem?_eq_none (by rw [h2.1]; omega)]

/-- Memory with `l` installed at `a`. -/
def putBytes (m : Memory) (a : Nat) (l : List Byte) : Memory := ⟨m.regions, Memory.install m.bytes a l⟩

theorem putBytes_keeps {m : Memory} {a : Nat} {l : List Byte} {P : Nat → Prop}
    (hP : ∀ x, P x → x < a ∨ a + l.length ≤ x) : Keeps P m (putBytes m a l) :=
  fun x hx => ⟨Memory.install_outside m.bytes _ _ x (hP x hx), fun _ => rfl⟩

theorem putBytes_ctx (m : Memory) (ctx : Word) (bs : List Byte) (hl : bs.length = 112) :
    CtxBytes (putBytes m ctx.toNat bs) ctx bs := by
  refine ⟨hl, fun i hi => ?_⟩
  rw [List.getElem?_eq_getElem (by omega)]
  exact Memory.install_get _ _ _ _ (by omega)

theorem sha256_eq {m1 m2 : List Byte} (h : sig (m1.map UInt8.ofBitVec) = sig (m2.map UInt8.ofBitVec)) :
    sha256 m1 = sha256 m2 := by
  simp only [sha256, digest_eq_of_sig h]

/-- The return frame of a call that writes `l` at `a` and returns `v`. -/
def retPut (s : PState) (v : Word) (a : Nat) (l : List Byte) : PState :=
  ⟨⟨(retState s v s.g).m.core, putBytes s.m.memory a l⟩, s.g⟩

theorem retPut_except (W : World) (s : PState) (v : Word) (a : Nat) (l : List Byte) (fp : Nat → Prop)
    (h : ∀ x, a ≤ x → x < a + l.length → fp x) : ReturnsExcept W fp s (retPut s v a l) :=
  ⟨(retState_returns W s v s.g).1, putBytes_keeps fun x hx => by
    by_contra hc
    exact hx.2 (h x (by omega) (by omega))⟩

theorem low32_one : low32 (1#64) = 1 := rfl

theorem sha_init_ok (W : World) (s : PState) : ∃ r, sha256InitStep shaRep W s r := by
  refine ⟨.ok (retPut s 1#64 (s.m.core.read .rdi).toNat (enc (sig []))), fun _ => ⟨_, rfl, ?_, ?_, rfl, rfl⟩⟩
  · exact retPut_except W s _ _ _ _ fun x h1 h2 => ⟨h1, by rw [enc_length _ (sig_ok _)] at h2; exact h2⟩
  · exact ⟨_, putBytes_ctx _ _ _ (enc_length _ (sig_ok _)), dec_enc _ (sig_ok _)⟩

theorem sha_update_ok (W : World) (s : PState) : ∃ r, sha256UpdateStep shaRep W s r := by
  by_cases hp : (∃ m, shaRep.holds s.m.memory (s.m.core.read .rdi) m) ∧
      ∃ d, s.m.memory.readBytes (s.m.core.read .rsi).toNat (s.m.core.read .rdx).toNat = some d
  · obtain ⟨⟨m0, bs0, hb0, hd0⟩, d0, hr0⟩ := hp
    let σ := (sig (m0.map UInt8.ofBitVec)).step (d0.map UInt8.ofBitVec)
    have hσ : σ.Ok := step_ok _ _
    refine ⟨.ok (retPut s 1#64 (s.m.core.read .rdi).toNat (enc σ)), fun _ => ⟨_, rfl, ?_, ?_, rfl, rfl⟩⟩
    · exact retPut_except W s _ _ _ _ fun x h1 h2 => ⟨h1, by rw [enc_length _ hσ] at h2; exact h2⟩
    · rintro m d ⟨bs, hb, hd⟩ hr
      obtain rfl := ctxBytes_unique hb hb0
      obtain rfl : d = d0 := Option.some.inj (hr.symm.trans hr0)
      refine ⟨_, putBytes_ctx _ _ _ (enc_length _ hσ), ?_⟩
      rw [dec_enc _ hσ, List.map_append, sig_append, ← hd, hd0]
  · exact ⟨.stop, fun h => absurd ⟨h.2.1, h.2.2.1⟩ hp⟩

theorem sha_final_ok (W : World) (s : PState) : ∃ r, sha256FinalStep shaRep W s r := by
  by_cases hp : (∃ m, shaRep.holds s.m.memory (s.m.core.read .rsi) m) ∧
      s.m.memory.Permitted .read (s.m.core.read .rdi).toNat 32
  · obtain ⟨⟨m0, bs0, hb0, hd0⟩, hrd⟩ := hp
    have hl : (sha256 m0).length = 32 := by simp [sha256, Silmaril.Crypto.SHA256.digest_length]
    refine ⟨.ok (retPut s 1#64 (s.m.core.read .rdi).toNat (sha256 m0)), fun _ => ⟨_, rfl, ?_, ?_, rfl, rfl⟩⟩
    · exact retPut_except W s _ _ _ _ fun x h1 h2 => Or.inr ⟨h1, by rw [hl] at h2; exact h2⟩
    · rintro m ⟨bs, hb, hd⟩
      obtain rfl := ctxBytes_unique hb hb0
      rw [sha256_eq (hd.symm.trans hd0)]
      unfold Memory.Permitted at hrd
      rw [Memory.checkSpan_iff] at hrd
      obtain ⟨ha, hw, hpm⟩ := hrd
      have := readWith_of_points (mem := (retPut s 1#64 (s.m.core.read .rdi).toNat (sha256 m0)).m.memory)
        (acc := .read) (l := sha256 m0) (a := (s.m.core.read .rdi).toNat)
        (by rw [hl]; exact hw) ha (fun k hk => ⟨hpm k (by rw [hl] at hk; exact hk),
          Memory.install_get _ _ _ _ hk⟩)
      simpa [Memory.readBytes, hl] using this
  · exact ⟨.stop, fun h => absurd ⟨h.2.1, h.2.2.2.1⟩ hp⟩

/-- **The `SHA256_*` contracts are satisfiable** (Task 2 of the dynamic-linking notes). -/
theorem sha_contracts_satisfiable : ∃ R : ShaRep, ∀ W s,
    (∃ r, sha256InitStep R W s r) ∧ (∃ r, sha256UpdateStep R W s r) ∧ (∃ r, sha256FinalStep R W s r) :=
  ⟨shaRep, fun W s => ⟨sha_init_ok W s, sha_update_ok W s, sha_final_ok W s⟩⟩

end Silmaril.Elf.Link.Dyn.Imports
