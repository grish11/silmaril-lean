module

public import Silmaril.Elf.Abi.Libm.Defs
public import Silmaril.Elf.Staged.Pinned.GlibcLibm236.Thms
public import Silmaril.Elf.Staged.Reader.Thms

/-! # glibc `libm.so.6` rows: file-fact lemmas

Each lemma turns a decidable check on the parse `A0` (`Pinned.GlibcLibm236.parses`) into the
fact a row states: a class (`Class.Holds`), `CodeOf`, the refusal of an IFUNC (`not_codeOf_ifunc`),
`Absent`, and the refusal of `Untouched` by an `IRELATIVE` relocation. -/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.Libm

open Silmaril.Elf Silmaril.Elf.Abi Silmaril.Elf.Abi.Libm
open Silmaril.Machine.Abi.Conformance

theorem parses : Parses F A0 := Silmaril.Elf.Staged.Pinned.GlibcLibm236.parses

/-- The parse of `F` is `A0`. -/
theorem parse_eq {A : File} (h : Parses F A) : A = A0 :=
  Option.some.inj (h.symm.trans parses)

theorem funcSym {i : Nat} {f : String} (h : funcSymB A0 i f = true) :
    ∃ s, SymbolAt F .dynsym i s ∧ s.name = nameOf f ∧ s.kind = 2 := by
  unfold funcSymB at h
  split at h
  · rename_i s hs
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨s, ⟨_, parses, hs⟩, h.1, h.2⟩
  · exact absurd h (by simp)

/-- **An IFUNC is refused**: if the lookup finds an `STT_GNU_IFUNC` definition, no code is the
function of that binding. -/
theorem not_codeOf_ifunc {b : Binding} {f : String} {d : Def}
    (hl : A0.select (b.sel f) = some (some d)) (hi : d.ifunc = true) (c : Code) :
    ¬ CodeOf F b f c := by
  rintro ⟨⟨d', ⟨A, hA, hs⟩, -, -, hf, -⟩, -⟩
  cases parse_eq hA
  rw [hl] at hs
  cases hs
  rw [hi] at hf
  cases hf

theorem absent_of {f : String} (h : absentB A0 f = true) : Absent F f := by
  refine ⟨_, parses, fun t s hs hn => ?_⟩
  simp only [absentB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  cases t
  · exact (h.1 s hs).resolve_left (not_not.mpr hn)
  · exact (h.2 s hs).resolve_left (not_not.mpr hn)

/-- **A checked class holds.** -/
theorem holds_of_check {f : String} {c : Class} (h : c.check A0 f = true) : c.Holds F f := by
  cases c with
  | plain v i val sz =>
    simp only [Class.check, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨⟨_, parses, h.1⟩, funcSym h.2⟩
  | ifunc v i =>
    simp only [Class.check] at h
    split at h
    · rename_i d hd
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact not_codeOf_ifunc hd h.2
    · cases h
  | absent => exact absent_of h

/-- `CodeOf` from the versioned lookup, the symbol entry, the bytes and the image. -/
theorem codeOf (b : Binding) (f : String) (c : Code) (i : Nat)
    (hb : b.table = .dynsym)
    (hl : A0.select (b.sel f) = some (some ⟨i, c.base.toNat + c.off, c.len, false, false⟩))
    (hs : funcSymB A0 i f = true) (hc : CodeAt F c.base.toNat c.bytes)
    (hd : ∀ d ∈ c.data, MappedAt F d.1.toNat d.2)
    (hi : c.image = A0.loads.map fun ph => (BitVec.ofNat 64 ph.virtualAddress, ph.memorySize)) :
    CodeOf F b f c :=
  ⟨⟨_, ⟨_, parses, hl⟩, rfl, rfl, rfl, rfl, hb ▸ funcSym hs⟩, hc, hd, ⟨_, parses, hi⟩⟩

/-- **An `R_X86_64_IRELATIVE` relocation refuses `Untouched` for every code.** -/
theorem not_untouched_of_irelative (h : (A0.relocs .dynamic).any (·.kind == 37) = true)
    (c : Code) : ¬ Untouched F c := by
  rintro ⟨A, hA, -, hr⟩
  cases parse_eq hA
  obtain ⟨r, hm, hk⟩ := List.any_eq_true.mp h
  obtain ⟨w, hw, -⟩ := hr r hm
  rw [beq_iff_eq.mp hk] at hw
  cases hw

end Silmaril.Proofs.Elf.Abi.Libm

end
