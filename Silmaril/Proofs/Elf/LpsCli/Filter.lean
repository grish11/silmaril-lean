module

public import Silmaril.Elf.LpsCli.Defs

@[expose] public section

/-! Proofs for `Silmaril.Elf.LpsCli` (the header `Silmaril.Elf.LpsCli.Thms` restates them). -/

namespace Silmaril.Proofs.Elf.LpsCli

open Silmaril.Elf.LpsCli
open Silmaril.Process.LPS
open Silmaril.Cli.Institution (Level Model Out1 Sen)

@[local simp] theorem cliBytes_lpsBytes (s : Silmaril.Cli.Bytes) : cliBytes (lpsBytes s) = s := by
  simp [cliBytes, lpsBytes, Function.comp_def]

@[local simp] theorem lpsBytes_cliBytes (b : List Byte) : lpsBytes (cliBytes b) = b := by
  simp [cliBytes, lpsBytes, Function.comp_def]

theorem exitOf_eq_none {tr : List Event} (h : ∀ e ∈ tr, ∀ c fs, e ≠ .exitEv c fs) :
    exitOf tr = none := by
  unfold exitOf
  split
  · rename_i c f hl
    have hm : Event.exitEv c f ∈ tr.filter Visible := List.mem_of_getLast? hl
    exact absurd rfl (h _ (List.mem_filter.mp hm).1 c f)
  · rfl

theorem stdoutOf_filterTrace (m out : List Byte) (fs : Fs.FileSystem) :
    stdoutOf (filterTrace m out fs) = out := by
  simp [stdoutOf, filterTrace, List.filterMap_append, List.filterMap_map]

theorem exitOf_filterTrace (m out : List Byte) (fs : Fs.FileSystem) :
    exitOf (filterTrace m out fs) = some 0 := by
  simp [exitOf, filterTrace, List.filter_append, Visible]

theorem out1Of_filterTrace (m out : List Byte) (fs : Fs.FileSystem) :
    out1Of (filterTrace m out fs) = some { stdout := cliBytes out, exit := 0 } := by
  simp [out1Of, exitOf_filterTrace, stdoutOf_filterTrace]

theorem out1Of_of_prefix {tr : List Event} {m out : List Byte} {fs : Fs.FileSystem} {o : Out1}
    (h : tr <+: filterTrace m out fs) (ho : out1Of tr = some o) :
    o = { stdout := cliBytes out, exit := 0 } := by
  unfold filterTrace at h
  rcases List.prefix_concat_iff.mp h with rfl | hp
  · rw [← filterTrace, out1Of_filterTrace] at ho
    exact (Option.some.inj ho).symm
  · have hn : exitOf tr = none := by
      refine exitOf_eq_none fun e he c f hc => ?_
      have := hp.subset he
      subst hc
      simp at this
    simp [out1Of, hn] at ho

theorem sat_filter_of_prefix {isa : Isa} {file : Silmaril.Formats.ELF.Bytes}
    {f : Silmaril.Cli.Bytes → Silmaril.Cli.Bytes}
    (h : ∀ s oracle refusals limit en inp records tr,
      StdinLaunch isa file s oracle en inp records →
      (behaviour isa file records oracle refusals limit en inp).traces tr →
      tr <+: filterTrace (lpsBytes s) (lpsBytes (f s)) inp.fs) :
    (lpsModel file isa).Sat (Sen.filter f) := by
  rintro s o ⟨tr, ⟨oracle, refusals, limit, en, inp, records, hl, ht⟩, ho⟩
  obtain rfl := out1Of_of_prefix (h _ _ _ _ _ _ _ _ hl ht) ho
  exact ⟨cliBytes_lpsBytes _, rfl⟩

end Silmaril.Proofs.Elf.LpsCli
