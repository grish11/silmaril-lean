module

public import Silmaril.Raw.Elf.Link.Dyn.Sha256sum.WitRunMem

/-! # GNU `sha256sum` witness: `main` entered with the library's guarantee, file tier

The file-tier counterpart of `WitMain`: for `argv = ["sha256sum", "f"]` (`argsF`), the entry
state `entMF` has the memory `memMA argsF []` (the kernel's memory `memW (stkOf argsF)`, the three
streams with an empty standard input, the fresh stack), `argc = 2`, `argv = sp0 + 8`. It satisfies
`MainLibF` (`mainLibF_entMF`), is entered from every gate state with the kernel's kept memory and
`fsBase` (`enters_entMF`), and has the resource invariant (`invR_entMF`).
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Sha256sum.Wit

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access Region Permissions)
open Silmaril.X86.Ext (loadN leBytes leValue)
open Silmaril.Elf.Link.Dyn
open Silmaril.Elf.Link.Dyn.Proc
open Silmaril.Elf.Link.Dyn.Proc.Witness
open Silmaril.Elf.Link.Dyn.Streams
open Silmaril.Elf.Link.Dyn.Streams.Total

/-- `argv = ["sha256sum", "f"]`. -/
abbrev argsF : List (List Byte) := [a00, f00]

theorem stkOf_af : stkOf argsF = pageOf 8192 [(4096, leBytes (BitVec.ofNat 64 2) 8),
    (4104, leBytes (sp0 + BitVec.ofNat 64 64) 8), (4112, leBytes (sp0 + BitVec.ofNat 64 74) 8),
    (argBase, a00 ++ [0#8] ++ (f00 ++ [0#8]))] := by
  simp [stkOf, f00, a00, List.range_succ]

theorem stkF_argv0 : ((stkOf argsF).drop 4104).take 8 = leBytes (sp0 + 64#64) 8 := by
  rw [stkOf_af]; decide +kernel
theorem stkF_argv1 : ((stkOf argsF).drop 4112).take 8 = leBytes (sp0 + 74#64) 8 := by
  rw [stkOf_af]; decide +kernel
theorem stkF_a0 : ((stkOf argsF).drop 4160).take 10 = a00 ++ [0#8] := by
  rw [stkOf_af]; decide +kernel
theorem stkF_f : ((stkOf argsF).drop 4170).take 2 = f00 ++ [0#8] := by
  rw [stkOf_af]; decide +kernel

theorem mem0F_read {o n : Nat} {l : List Byte} (hl : ((stkOf argsF).drop o).take n = l) (ho : o + n ≤ 8192) :
    (mem0A argsF).readBytes (stackLo + o) n = some l := by
  rw [← hl]
  exact read_page (fun j hj => memW_stk _ hj)
    (fun j hj => mem0_stackP (Or.inl rfl) (by omega) (by omega)) (by rw [stkOf_length]; exact ho)
    (by rw [stackLo_eq]; omega)

theorem e_rsi2 : (sp0 + 16#64).toNat = 0x7ffffffde010 := by decide
theorem e_f : (sp0 + 74#64).toNat = 0x7ffffffde04a := by decide

theorem hdF : 64 + ([] : List Byte).length ≤ S0 := by simp [S0]

theorem memF_argv0 : loadN (memMA argsF []) (sp0 + 8#64) 8 = some (sp0 + 64#64) := by
  refine memM_loadN [] hdF (fun k hk' => by rw [e_rsi]; exact not_new_hi (by omega)) ?_
  rw [e_rsi, show (0x7ffffffde008 : Nat) = stackLo + 4104 by rw [stackLo_eq]]
  exact mem0F_read stkF_argv0 (by decide)

theorem memF_argv1 : loadN (memMA argsF []) (sp0 + 16#64) 8 = some (sp0 + 74#64) := by
  refine memM_loadN [] hdF (fun k hk' => by rw [e_rsi2]; exact not_new_hi (by omega)) ?_
  rw [e_rsi2, show (0x7ffffffde010 : Nat) = stackLo + 4112 by rw [stackLo_eq]]
  exact mem0F_read stkF_argv1 (by decide)

theorem memF_a0 : CStr (memMA argsF []) (sp0 + 64#64) a00 := by
  refine ⟨by decide, ?_⟩
  show (memMA argsF []).readBytes (sp0 + 64#64).toNat 10 = some (a00 ++ [0#8])
  rw [memM_read [] hdF (fun k hk' => by rw [e_a0]; exact not_new_hi (by omega)), e_a0,
    show (0x7ffffffde040 : Nat) = stackLo + 4160 by rw [stackLo_eq]]
  exact mem0F_read stkF_a0 (by decide)

theorem memF_f : CStr (memMA argsF []) (sp0 + 74#64) f00 := by
  refine ⟨by decide, ?_⟩
  show (memMA argsF []).readBytes (sp0 + 74#64).toNat 2 = some (f00 ++ [0#8])
  rw [memM_read [] hdF (fun k hk' => by rw [e_f]; exact not_new_hi (by omega)), e_f,
    show (0x7ffffffde04a : Nat) = stackLo + 4170 by rw [stackLo_eq]]
  exact mem0F_read stkF_f (by decide)

/-- `main`'s registers on the file tier: `rsp = rspT`, `argc = 2`, `argv = sp0 + 8`, `envp = a3`. -/
def coreMF (f a3 : Word) : State :=
  ⟨fun r => if r = .rsp then rspT else if r = .rdi then 2#64 else if r = .rsi then sp0 + 8#64
    else if r = .rdx then a3 else 0, f, ⟨none, none, none, none, none, none⟩, fs0⟩

/-- **`main`'s entry state on the file tier.** -/
def entMF (f a3 : Word) (g : Ghost) : PState := ⟨⟨coreMF f a3, memMA argsF []⟩, g⟩

section
variable (f a3 : Word)
theorem coreMF_rsp : (coreMF f a3).read .rsp = rspT := by simp [coreMF, State.read]
theorem coreMF_rdi : (coreMF f a3).read .rdi = 2#64 := by simp [coreMF, State.read]
theorem coreMF_rsi : (coreMF f a3).read .rsi = sp0 + 8#64 := by simp [coreMF, State.read]
theorem coreMF_rdx : (coreMF f a3).read .rdx = a3 := by simp [coreMF, State.read]
end

set_option maxRecDepth 100000 in
/-- **`MainLibF` holds at `entMF`.** -/
theorem mainLibF_entMF (fs : Silmaril.Apps.Sha256sum.Bytes → Silmaril.Apps.Sha256sum.ReadResult)
    (f a3 : Word) (g : Ghost) :
    MainLibF (E0 fs) Wf b0 lb0 (Cm fs) inF (stdinSt []) (entMF f a3 g) (sp0 + 64#64) a00
      [(sp0 + 74#64, f00)] guard0 := by
  have hrsp : (entMF f a3 g).m.core.read .rsp = rspT := coreMF_rsp f a3
  have hrsi : (entMF f a3 g).m.core.read .rsi = sp0 + 8#64 := coreMF_rsi f a3
  have hrdi : (entMF f a3 g).m.core.read .rdi = 2#64 := coreMF_rdi f a3
  have hfs : (entMF f a3 g).m.core.fsBase = fs0 := rfl
  have hm : (entMF f a3 g).m.memory = memMA argsF [] := rfl
  have hvout : lb0 + 0x2056a8#64 = BitVec.ofNat 64 (0x7ffff7e04000 + 0x16a8) := by decide
  have hverr : lb0 + 0x2056a0#64 = BitVec.ofNat 64 (0x7ffff7e04000 + 0x16a0) := by decide
  refine
    { lo := by rw [hrsp]; show A0 + K0 * S0 + 4096 ≤ rspT.toNat; rw [rspT_toNat]; simp only [A0, K0, S0]; omega
      env := by
       rw [hm]
       exact
        { out := file_out []
          err := file_err []
          inp := file_in [] hdF
          vars :=
            { out := by rw [hvout]; exact lib_read [] hdF lib_out (by decide)
              err := by rw [hverr]; exact lib_read [] hdF lib_err (by decide)
              kept := fun k hk => by rw [kept_iff, e_verr]; omega
              bound := by rw [e_verr]; omega }
          np := fun a h => by
            rcases h with h | h
            · refine ⟨fun hA => ?_, memM_img [] h⟩
              have hA' : Arena a := hA
              rw [img_iff] at h; simp only [Arena, A0, K0, S0] at hA'; omega
            · have hb : 0x7ffff7e04000 ≤ a ∧ a < 0x7ffff7e06000 := by
                rcases h with h | h
                · rw [pin_iff] at h; omega
                · rw [opt_iff] at h; omega
              refine ⟨fun hA => ?_, memM_lib [] (Or.inl rfl) (by rw [libLo_eq]; omega) (by rw [libLo_eq]; omega)⟩
              have hA' : Arena a := hA
              simp only [Arena, A0, K0, S0] at hA'; omega
          wr := fun a h => by
            have hb : 0x7ffff7e04000 ≤ a ∧ a < 0x7ffff7e06000 := by
              rcases h with h | h
              · rw [pin_iff] at h; omega
              · rw [opt_iff] at h; omega
            exact memM_lib [] (Or.inr rfl) (by rw [libLo_eq]; omega) (by rw [libLo_eq]; omega) }
      hC := fun a h => by
        left; rw [hrsp, rspT_toNat]
        rcases h with h | h
        · rw [pin_iff] at h; omega
        · rw [opt_iff] at h; omega
      pinC := fun a h => Or.inl h
      pinK := fun a h hk => by rw [pin_iff] at h; rw [kept_iff] at hk; omega
      optC := fun a h => Or.inr h
      optK := fun a h hk => by rw [opt_iff] at h; rw [kept_iff] at hk; omega
      optL := fun a h => by rw [opt_iff] at h; rw [hrsp, rspT_toNat]; omega
      opt := by show (lb0 + 0x204248#64).toNat + 4 < 2 ^ 64; rw [e_opt]; omega
      lbB := by rw [lb0_toNat]; omega
      imgVar := fun a h hv => by rw [img_iff] at h; rw [var_iff] at hv; omega
      argsImg := fun a h hi => by rw [args_iff] at h; rw [img_iff] at hi; omega
      argv := fun m hk i hi => by
        rw [hm] at hk; rw [hrsi]
        have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
        rcases hi2 with rfl | rfl
        · refine ⟨sp0 + 64#64, ?_, ?_⟩
          · rw [show sp0 + 8#64 + BitVec.ofNat 64 (8 * 0) = sp0 + 8#64 by decide,
              loadN_keeps hk (fun k hk' => by rw [args_iff, e_rsi]; omega)]
            exact memF_argv0
          · show CStr m (sp0 + 64#64) a00
            exact cstr_keeps hk memF_a0 (fun j hj => by
              rw [args_iff, e_a0]; simp only [a00, List.length_cons, List.length_nil] at hj; omega)
        · refine ⟨sp0 + 74#64, ?_, ?_⟩
          · rw [show sp0 + 8#64 + BitVec.ofNat 64 (8 * 1) = sp0 + 16#64 by decide,
              loadN_keeps hk (fun k hk' => by rw [args_iff, e_rsi2]; omega)]
            exact memF_argv1
          · show CStr m (sp0 + 74#64) f00
            exact cstr_keeps hk memF_f (fun j hj => by
              rw [args_iff, e_f]; simp only [f00, List.length_cons, List.length_nil] at hj; omega)
      argv0 := by rw [hm, hrsi]; exact memF_argv0
      argv0k := fun k hk => by rw [hrsi, kept_iff, e_rsi]; omega
      a0s := by rw [hm]; exact memF_a0
      a0k := fun j hj => by
        rw [kept_iff, e_a0]; simp only [a00, List.length_cons, List.length_nil] at hj; omega
      a0nz := by decide
      noSlash := by decide
      guard := by
        rw [hm, hfs]
        refine memM_loadN [] hdF (fun k hk' => by rw [e_g]; exact not_new_kept (by omega) (by omega)) ?_
        rw [e_g, show (0x7ffff7fb0028 : Nat) = fs0.toNat + 0x28 by rw [fs0_toNat]]
        exact mem0_guard
      guardk := fun j hj => by rw [hfs, kept_iff, e_g]; omega
      guardImg := fun j hj h => by rw [hfs, img_iff, e_g] at h; omega
      args := by
        rw [hm, hrsi, show sp0 + 8#64 + 8#64 = sp0 + 16#64 by decide]
        refine ⟨memF_argv1, fun j hj => by rw [args_iff, e_rsi2]; omega, memF_f,
          fun j hj => by rw [args_iff, e_f]; simp only [f00, List.length_cons, List.length_nil] at hj; omega,
          trivial⟩
      ne := by simp
      argc := by rw [hrdi]; decide
      argcLim := by decide
      avLim := by rw [hrsi, e_rsi]; decide }

/-- `main` is entered at `entMF`: the gate word on a fresh aligned stack, the kept memory and
`fsBase` as the kernel left them. -/
theorem enters_entMF (u : PState) (f a3 : Word) (g : Ghost)
    (hu : Keeps Wf.Kept (s0 argsF).m.memory u.m.memory) (hfs : u.m.core.fsBase = fs0) :
    Enters Wf u (entMF f a3 g) f := by
  have hrsp : (entMF f a3 g).m.core.read .rsp = rspT := coreMF_rsp f a3
  refine ⟨rfl, by rw [hrsp, rspT_toNat], ?_, ?_, ?_, hfs.symm⟩
  · rw [hrsp]
    show (memMA argsF []).readBytes rspT.toNat 8 = some gateBytes
    rw [← gateBytes_length]
    refine read_of (by rw [gateBytes_length, rspT_toNat]; omega)
      (fun k hk => memM_stk2 [] (Or.inl rfl) (by rw [rspT_toNat]; simp only [stk2Lo]; omega)
        (by rw [gateBytes_length] at hk; rw [rspT_toNat]; simp only [stk2Lo]; omega)) (fun k hk => ?_)
    exact Memory.install_get _ _ _ _ hk
  · rw [hrsp]
    refine ⟨by rw [rspT_toNat]; omega, by rw [rspT_toNat]; omega, fun a h1 h2 => ?_⟩
    rw [rspT_toNat] at h1 h2
    refine ⟨memM_stk2 [] (Or.inl rfl) (by simp only [stk2Lo]; omega) (by simp only [stk2Lo]; omega),
      memM_stk2 [] (Or.inr rfl) (by simp only [stk2Lo]; omega) (by simp only [stk2Lo]; omega), fun hk => ?_⟩
    rw [kept_iff] at hk; omega
  · exact (Keeps.symm' hu).trans ((keepsNew (args := argsF) [] hdF).mono fun a h => kept_not_new h)

/-- The resource invariant at `entMF`: no block below the arena, the three standard streams. -/
theorem invR_entMF (f a3 : Word) (g : Ghost) : InvR (entMF f a3 g) := by
  intro _
  refine ⟨⟨[], by simp, by simp, fun x hx hr => ?_⟩, ⟨[0, 1, 2], by simp, fun f' st hf => ?_⟩⟩
  · have := memM_low (args := argsF) [] hx
    change (memMA argsF []).permits .read x = true at hr
    rw [this] at hr; cases hr
  · obtain ⟨k, hk, he⟩ := hf.1
    obtain ⟨-, -, hp⟩ := perm_of_read hf.2.2.1
    have hk3 : k < 3 := by
      by_contra hc
      have hp0 := hp 0 (by omega)
      change (memMA argsF []).permits .read (f'.toNat + 0) = true at hp0
      have hKS : k < 15 := hk
      have := memM_slot_nr (args := argsF) [] (a := f'.toNat + 0) (by rw [he]; unfold A0 S0; omega)
        (by rw [he, loA_eq]; unfold A0 S0; omega)
      rw [hp0] at this; cases this
    refine ⟨k, by simp; omega, hk, ?_⟩
    apply BitVec.eq_of_toNat_eq
    rw [he, slotW_toNat (by unfold K0; omega)]

end Silmaril.Elf.Link.Dyn.Sha256sum.Wit
