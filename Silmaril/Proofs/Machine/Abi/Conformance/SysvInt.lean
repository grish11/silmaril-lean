module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.Machine.Abi.Win64.Thms
public import Silmaril.X86.FnContract.Thms

/-!
# The System V INTEGER fragment: entry, return and result lemmas

What a proof of a `sysvInt` row needs from `Ffi.Entry`/`Ffi.Return`/`Ffi.ResultAt`: the
function-contract entry obligations, a contract result as a System V return, and the read-back of
32-bit results. These are the lemmas of `Machine.Abi.OpenMachine` (`abiEntry_of_entry`,
`return_of_result`, `chunk32_iff`, `resultAt_int32`), restated for any machine whose core and
memory are the state's: that module's import closure includes the System V adapter
`Silmaril.X86.FnContract.SystemV`, which cannot be loaded together with the
`Silmaril.Machine.X86` copies of the same declarations that other registered modules load.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance.SysvInt

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.Machine.SystemV.Abi
open Silmaril.Machine.Abi.SystemV (Proto vocab sysv)
open Silmaril.Machine.Abi.Conformance

variable {p : Proto}

theorem retAddr_of_entry {a : vocab.Args p} {s : Ffi.State} (entry : sysvInt.conv.Entry p a s) :
    ∃ exit, s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
        some (Silmaril.Machine.LittleEndian.encodeWords [exit]) ∧
      Silmaril.X86.FnContract.retOf s.machine.core s.machine.memory = exit ∧
      s.direction = false ∧ s.x87Mode = true := by
  obtain ⟨exit, e⟩ := entry
  exact ⟨exit, e.returnAddress, Silmaril.X86.FnContract.retOf_of_readBytes e.returnAddress,
    e.direction, e.x87Mode⟩

/-- A System V entry state meets the function-contract entry obligations. -/
theorem abiEntry_of_entry {a : vocab.Args p} {s : Ffi.State} (entry : sysvInt.conv.Entry p a s) :
    Silmaril.X86.FnContract.AbiEntry s.machine.core s.machine.memory := by
  obtain ⟨exit, e⟩ := entry
  have align := e.alignment
  change ((s.machine.core.read .rsp).toNat + 8) % 16 = 0 at align
  have ra : s.machine.memory.readBytes (s.machine.core.read .rsp).toNat 8 =
      some (Silmaril.Machine.LittleEndian.encodeWords [exit]) := e.returnAddress
  refine ⟨by omega, ?_⟩
  rw [Silmaril.X86.FnContract.retOf_of_readBytes ra]
  exact ra

/-- A function-contract result from a System V entry state is a System V return, on a machine
whose core and memory are the state's. -/
theorem return_of_result {M : Mach} (hc : ∀ m, M.core m = m.core) (hm : ∀ m, M.mem m = m.memory)
    {S : Silmaril.X86.FnContract.Spec MState} {a : vocab.Args p} {s : Ffi.State}
    {t : MState} (entry : sysvInt.conv.Entry p a s) (res : S.Result M s.machine t) :
    sysvInt.conv.Return p s { s with machine := t } := by
  obtain ⟨exit, ra, hret, dir, x87⟩ := retAddr_of_entry entry
  refine ⟨exit, ra, ?_⟩
  have pc := res.abi.pc
  have st := res.abi.stack
  have cs := res.abi.calleeSaved
  rw [hc, hc] at pc st cs
  rw [hm] at pc
  exact ⟨pc.trans hret, st, cs, dir, x87, rfl, rfl, rfl⟩

theorem bytes4_inj {x y : BitVec 32}
    (h : Ffi.bytesOfNat x.toNat 0 4 = Ffi.bytesOfNat y.toNat 0 4) : x = y := by
  have hx := x.isLt
  have hy := y.isLt
  simp only [Ffi.bytesOfNat, List.range_succ, List.range_zero, List.nil_append,
     List.map_cons, List.map_nil, List.cons_append,
    List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  simp only [UInt8.ofNat, UInt8.ofBitVec.injEq] at h0 h1 h2 h3
  have t := fun {a b : Nat} (e : BitVec.ofNat 8 a = BitVec.ofNat 8 b) =>
    congrArg BitVec.toNat e
  have e0 := t h0; have e1 := t h1; have e2 := t h2; have e3 := t h3
  simp only [BitVec.toNat_ofNat] at e0 e1 e2 e3
  simp only [Nat.zero_add, Nat.mul_zero, Nat.mul_one, Nat.pow_zero, Nat.div_one] at e0 e1 e2 e3
  apply BitVec.eq_of_toNat_eq
  omega

theorem chunk32_iff (s : Ffi.State) (r : Reg) (v : BitVec 32) :
    Ffi.ChunksAt s (Ffi.bytesOfNat (v.setWidth 64).toNat 0 4) [⟨0, 4, .gp r⟩] ↔
      (s.machine.core.read r).setWidth 32 = v := by
  have wide : (v.setWidth 64).toNat = v.toNat := by
    have := v.isLt
    simp only [BitVec.toNat_setWidth]
    omega
  have len : ∀ n, (Ffi.bytesOfNat n 0 4).length = 4 := by simp [Ffi.bytesOfNat]
  rw [wide]
  simp only [Ffi.ChunksAt, List.mem_singleton, forall_eq, Ffi.locationBytes, len,
    Nat.zero_add, le_refl, true_and, List.drop_zero, List.take_of_length_le (le_of_eq (len _)),
    show (4 : Nat) ≤ 8 from by decide, ite_true, Option.some.injEq]
  exact ⟨bytes4_inj, fun h => h ▸ rfl⟩

theorem resultAt_int32 (args : List Silmaril.C.Api.Scalar)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State) (r : BitVec 32) :
    sysvInt.conv.ResultAt ⟨⟨args, some .int32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r := by
  refine (Silmaril.Machine.Abi.Win64.sysv_resultAt_iff _ _ _ _ _).trans ?_
  constructor
  · rintro ⟨w, enc, ch⟩
    change w = _ at enc
    subst enc
    exact (chunk32_iff s' .rax r).1 ch
  · exact fun e => ⟨_, rfl, (chunk32_iff s' .rax r).2 e⟩

theorem resultAt_uint32 (args : List Silmaril.C.Api.Scalar)
    (h : args.length ≤ Silmaril.Machine.Abi.SystemV.maxArity) (s s' : Ffi.State) (r : BitVec 32) :
    sysvInt.conv.ResultAt ⟨⟨args, some .uint32⟩, h⟩ s s' r ↔
      (s'.machine.core.read .rax).setWidth 32 = r := by
  refine (Silmaril.Machine.Abi.Win64.sysv_resultAt_iff _ _ _ _ _).trans ?_
  constructor
  · rintro ⟨w, enc, ch⟩
    change w = _ at enc
    subst enc
    exact (chunk32_iff s' .rax r).1 ch
  · exact fun e => ⟨_, rfl, (chunk32_iff s' .rax r).2 e⟩

end Silmaril.Proofs.Machine.Abi.Conformance.SysvInt

end
