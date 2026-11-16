module

public import Silmaril.Sim.WasiBridge.Cli.Lps.Defs
public import Silmaril.Sim.WasiBridge.Cli.Sha256sum.Thms
public import Silmaril.Elf.LpsCli.Sha256sum.Thms

/-!
# Static executables under LPS in the ELF ≡ WASI bridge

PROVED (standard axioms):

* `out1_obsTrace`: the bridge's `L1` observation of an LPS trace is `LpsCli.out1Of`;
* **`lpsModel_eq`**: `LpsCli.lpsModel file isa = traceModel (lpsTraces file isa)`;
* **`wasiSha256_of_static`**: a WASI preview1 program whose traces are `ElfWasiEquiv` to those of
  `sha256sum-min` under LPS (stdin by stdin) meets `Std.sha256Stdin`, i.e. it discharges
  `Task.wasiSha256`;
* `wasi_agrees_glibc_of_static`: such a WASI program agrees run by run with the real GNU
  `sha256sum` on glibc (and, by `static_agrees_glibc`, with `sha256sum-min`).

So the chain WASI ≡ static ELF (stated, `ElfWasiEquiv`) ⊨ `Std.sha256Stdin` (proved) ⫤ glibc
(proved) relates all three builds through one sentence. The converse direction (a proved WASI
`sha256sum` gives the static one) is `sha256_of_wasi` with `P := lpsTraces …`; it is redundant
for `sha256sum-min`, whose own proof is unconditional.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Lps

open Silmaril.Process.LPS (Event)
open Silmaril.Cli.Institution (Level Model Sen Out1)
open Silmaril.Elf.LpsCli

/-- One observable per visible event. -/
def obs1 : Event → Obs
  | .readEv ch b => .rd ch.toNat b
  | .writeEv ch b => .wr ch.toNat b
  | .exitEv c _ => .exit c.toNat
  | .killEv .. => .rd 0 0

theorem obsTrace_eq (tr : List Event) : obsTrace tr = (tr.filter Visible).map obs1 := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    cases e <;> simp_all [obsTrace, obsOfEvent, Visible, obs1, List.filter_cons]

theorem writtenOn_obsTrace (tr : List Event) : writtenOn 1 (obsTrace tr) = stdoutOf tr := by
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    cases e <;> simp_all [obsTrace, obsOfEvent, writtenOn, stdoutOf, List.filterMap_cons]

theorem endCode_obsTrace (tr : List Event) :
    endCode (obsTrace tr) = (exitOf tr).map (·.toNat) := by
  rw [obsTrace_eq, endCode, exitOf, List.getLast?_map]
  rcases (tr.filter Visible).getLast? with _ | e
  · rfl
  · cases e <;> rfl

/-- **The bridge's observation of an LPS trace is `LpsCli.out1Of`.** -/
theorem out1_obsTrace (tr : List Event) : out1 (obsTrace tr) = out1Of tr := by
  simp only [out1, out1Of, endCode_obsTrace, writtenOn_obsTrace, Option.map_map]
  rfl

/-- **`lpsModel` is a trace model.** -/
theorem lpsModel_eq (file : Silmaril.Formats.ELF.Bytes) (isa : Isa) :
    lpsModel file isa = traceModel (lpsTraces file isa) := by
  ext s o
  constructor
  · rintro ⟨tr, h, ho⟩
    exact ⟨obsTrace tr, ⟨tr, h, rfl⟩, by rw [out1_obsTrace]; exact ho⟩
  · rintro ⟨t, ⟨tr, h, rfl⟩, ho⟩
    exact ⟨tr, h, by rw [← out1_obsTrace]; exact ho⟩

/-- The traces of `sha256sum-min` under LPS. -/
abbrev staticTraces : Silmaril.Cli.Bytes → List Obs → Prop :=
  lpsTraces Silmaril.Process.LPS.Problems.GnuSha256sum.file ext8

theorem staticTraces_sat : (traceModel staticTraces).Sat Silmaril.Cli.Institution.Std.sha256Stdin := by
  rw [← lpsModel_eq]; exact Sha256sum.staticModel_sat

/-- **A WASI program equivalent to `sha256sum-min` discharges `Task.wasiSha256`.** -/
theorem wasiSha256_of_static {W : Silmaril.Cli.Bytes → P1Sem} {S : Subset}
    (hE : ∀ s, ElfWasiEquiv (staticTraces s) (W s) S) : Task.wasiSha256 W S :=
  (sat_iff_of_elfWasiEquiv hE _).mp staticTraces_sat

/-- **Such a WASI program agrees with GNU `sha256sum` on glibc.** -/
theorem wasi_agrees_glibc_of_static {W : Silmaril.Cli.Bytes → P1Sem} {S : Subset}
    (hE : ∀ s, ElfWasiEquiv (staticTraces s) (W s) S) {s : Silmaril.Cli.Bytes} {o o' : Out1}
    (h : (p1Model W S).Run s o) (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') :
    o = o' :=
  Silmaril.Cli.Institution.Std.sha256Stdin_agree (wasiSha256_of_static hE)
    Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel_std h h'

end Silmaril.Sim.WasiBridge.Lps
