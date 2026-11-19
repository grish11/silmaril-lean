module

public import Silmaril.Sim.WasiBridge.Tv.Thms
public import Silmaril.Sim.WasiBridge.Cli.Sha256sum.Thms

/-!
# sha256sum by translation validation (level `L1`)

The TV route to `Std.sha256Stdin` for an x86 build (a static musl `sha256sum`, an optimisation
level of the GNU one, or the same binary inside the Wasm simulator), as transition systems `A`
per stdin: a certificate `Cert (A s) (B s)` to an operational model `B s` of a WASI preview1
`sha256sum` (ended-equivalent to its trace semantics `W s`), and the WASI program meeting the
sentence (`Task.wasiSha256`).

PROVED (standard axioms), conditional on `Task.wasiSha256`:

* `sha256_of_cert`: the certified build meets `Std.sha256Stdin`;
* `sha256_cert_agrees_glibc`: every run of it agrees with every run of GNU `sha256sum` on glibc
  on the same stdin (equal stdout and exit code);
* `sha256_cert_native`: given `Task.nativeInTraces`, a full model (the binary under its own
  process model) meets the lifted sentence.

The certificates themselves (per binary: `Slice`s to sliced simulators, block-level couplings in
the style of silmaril's `TVIR.Sim`) are the open work; see `Silmaril.Sim.WasiBridge.Tv.Defs`.
-/

@[expose] public section

namespace Silmaril.Sim.WasiBridge.Tv

open Silmaril.Cli (Bytes)
open Silmaril.Cli.Institution (Level Model Sen Out1)
open Silmaril.Cli.Institution.Std (sha256Stdin)

theorem sha256_of_cert {A B : Bytes → Lts} {W : Bytes → P1Sem} {S : Subset}
    (hW : Task.wasiSha256 W S) (c : ∀ s, Cert (A s) (B s))
    (hB : ∀ s, EndedEquiv (B s).traces ((W s).obs S)) :
    (traceModel fun s => (A s).traces).Sat sha256Stdin :=
  (sat_iff_of_elfWasiEnded (fun s => elfWasiEnded_of_cert (c s) (hB s)) _).mpr hW

/-- **A certified x86 build agrees with GNU `sha256sum` on glibc**, run by run. -/
theorem sha256_cert_agrees_glibc {A B : Bytes → Lts} {W : Bytes → P1Sem} {S : Subset}
    (hW : Task.wasiSha256 W S) (c : ∀ s, Cert (A s) (B s))
    (hB : ∀ s, EndedEquiv (B s).traces ((W s).obs S)) {s : Bytes} {o o' : Out1}
    (h : (traceModel fun s => (A s).traces).Run s o)
    (h' : Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel.Run s o') : o = o' :=
  Silmaril.Cli.Institution.Std.sha256Stdin_agree (sha256_of_cert hW c hB)
    Silmaril.Elf.Link.Dyn.Sha256sum.stdinModel_std h h'

theorem sha256_cert_native {M : Model Level.full.sig} {A B : Bytes → Lts} {W : Bytes → P1Sem}
    {S : Subset} (hW : Task.wasiSha256 W S) (c : ∀ s, Cert (A s) (B s))
    (hB : ∀ s, EndedEquiv (B s).traces ((W s).obs S))
    (hT : Task.nativeInTraces M fun s => (A s).traces) : M.Sat (Level.lift sha256Stdin) :=
  native_sat_of_wasi_ended hW (fun s => elfWasiEnded_of_cert (c s) (hB s)) hT

end Silmaril.Sim.WasiBridge.Tv

/-- info: 'Silmaril.Sim.WasiBridge.Tv.sha256_cert_agrees_glibc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.sha256_cert_agrees_glibc
/-- info: 'Silmaril.Sim.WasiBridge.Tv.sha256_cert_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Silmaril.Sim.WasiBridge.Tv.sha256_cert_native
