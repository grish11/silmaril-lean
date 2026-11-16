module

public import Silmaril.Project.ConsequenceSystems.WasmSeq.Defs
public meta import Silmaril.Project.ConsequenceSystems.Matrix.Defs
public import Silmaril.Project.Shapes.Consequence.Thms
public import Silmaril.Wasi.Component.Consequence.Interp.Thms
public import ProjectSelfTest.WasmAcceptors
public import ProjectSelfTest.Consequence.Wasm

/-!
# The `sil project` self-test: registered Wasm artifacts through a partial interpretation

`member_check.wasm` and `empty_check.wasm` read through `wasm.core.seq` (the protocol track's
`coreInterp`, a partial core `Interp`) at the configuration `memberEnv`: `Profile.spec`, every
Core host (`allHosts`), the export `check` and the codec `memberEnc`. The systems are
multiple-conclusion relations between byte lists.

* Both are **defined** (`artifact_defined`, THM): the bytes decode (the values' `.is`
  certificates) and `coreInterp` reads every module.
* `member_check` is sound for single-succedent membership `Δ = [c] ∧ c ∈ Γ`, and complete for it
  within `Γ.length + 1 ≤ 2 ^ 32 - 1` (a nonempty host set). The answers apply the protocol
  theorems `member_sound` and `member_completeOn`, stated for `MemberCheck`'s bytes, through
  `coreBytesInterp_member` (those bytes decode to `MemberCheck.prog`) and the registered value's
  `.is` certificate (its bytes decode to the same module).
* `empty_check` is **defined and empty**: it derives nothing (`coreBytesInterp_empty`).
-/

namespace ProjectSelfTest.Consequence.WasmSeq

open Silmaril.Consequence Silmaril.Wasi.Consequence

@[expose] public section

/-- The configuration: `Profile.spec`, every Core host, the export `check`, the codec `memberEnc`. -/
def memberEnv : CoreConfig :=
  memberConfig Silmaril.Wasm.Numerics.Profile.spec Silmaril.Project.Languages.WasmExport.allHosts

/-- Single-succedent membership: `Γ ⊢ [c]` iff `c ∈ Γ`. -/
def singleMem : System (List UInt8) (List UInt8) := fun Γ Δ => ∃ c, Δ = [c] ∧ c ∈ Γ

end

end ProjectSelfTest.Consequence.WasmSeq

silmaril consequence_system silmaril.selftest.consequence.wasm_seq.member_check (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.member_check) (interpretation := wasm.core.seq)
  (env := ProjectSelfTest.Consequence.WasmSeq.memberEnv)
  (title := "member_check.wasm through coreInterp at memberEnv (Γ ⊢ Δ, byte lists)")
silmaril consequence_system silmaril.selftest.consequence.wasm_seq.empty_check (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.empty_check) (interpretation := wasm.core.seq)
  (env := ProjectSelfTest.Consequence.WasmSeq.memberEnv)
  (title := "empty_check.wasm through coreInterp at memberEnv (Γ ⊢ Δ, byte lists)")
silmaril consequence_system silmaril.selftest.consequence.wasm_seq.single_mem :=
  ProjectSelfTest.Consequence.WasmSeq.singleMem (title := "Γ ⊢ [c] iff c ∈ Γ (bytes)")

namespace ProjectSelfTest.Consequence.WasmSeq

open Silmaril.Consequence Silmaril.Wasi.Consequence Silmaril.Project.ConsequenceSystems

/-- The registered `member_check` system is `coreSeq` of `MemberCheck.prog` at `memberEnv`. -/
public theorem member_eq : silmaril.selftest.consequence.wasm_seq.member_check =
    coreSeq memberEnv.P memberEnv.Hosts Silmaril.Wasm.Examples.MemberCheck.prog memberEnv.name memberEnv.enc :=
  artifactSystem_of_is ProjectSelfTest.WasmAcceptors.member_check_is_prog

/-- The registered `empty_check` system is `coreSeq` of `EmptyCheck.prog` at `memberEnv`. -/
public theorem empty_eq : silmaril.selftest.consequence.wasm_seq.empty_check =
    coreSeq memberEnv.P memberEnv.Hosts Silmaril.Wasm.Examples.EmptyCheck.prog memberEnv.name memberEnv.enc :=
  artifactSystem_of_is ProjectSelfTest.WasmAcceptors.empty_check_is_prog

end ProjectSelfTest.Consequence.WasmSeq

open ProjectSelfTest.Consequence.WasmSeq Silmaril.Consequence Silmaril.Wasi.Consequence
  Silmaril.Project.Shapes.Consequence in
section

silmaril instance silmaril.selftest.consequence.wasm_seq.member_defined (expect := THM)
  (title := "member_check.wasm decodes and coreInterp is defined on it at memberEnv") :=
  silmaril.shapes.consequence.artifact_defined (X := silmaril.selftest.wasm_acceptors.member_check)
  (I := Silmaril.Wasi.Consequence.coreInterp) (e := ProjectSelfTest.Consequence.WasmSeq.memberEnv)

@[answers "silmaril.selftest.consequence.wasm_seq.member_defined" thm]
public theorem member_defined : silmaril.selftest.consequence.wasm_seq.member_defined :=
  ⟨_, ProjectSelfTest.WasmAcceptors.member_check_is_prog, rfl⟩

silmaril instance silmaril.selftest.consequence.wasm_seq.empty_defined (expect := THM)
  (title := "empty_check.wasm decodes and coreInterp is defined on it at memberEnv") :=
  silmaril.shapes.consequence.artifact_defined (X := silmaril.selftest.wasm_acceptors.empty_check)
  (I := Silmaril.Wasi.Consequence.coreInterp) (e := ProjectSelfTest.Consequence.WasmSeq.memberEnv)

@[answers "silmaril.selftest.consequence.wasm_seq.empty_defined" thm]
public theorem empty_defined : silmaril.selftest.consequence.wasm_seq.empty_defined :=
  ⟨_, ProjectSelfTest.WasmAcceptors.empty_check_is_prog, rfl⟩

silmaril instance silmaril.selftest.consequence.wasm_seq.member_sound (expect := THM)
  (title := "member_check.wasm (coreInterp) is sound for single-succedent membership, every host set") :=
  silmaril.shapes.consequence.sound_at (S := silmaril.selftest.consequence.wasm_seq.member_check)
  (T := ProjectSelfTest.Consequence.WasmSeq.singleMem)

@[answers "silmaril.selftest.consequence.wasm_seq.member_sound" thm]
public theorem member_sound_at : ∀ Γ Δ,
    SoundAt silmaril.selftest.consequence.wasm_seq.member_check singleMem Γ Δ := fun Γ Δ h =>
  Silmaril.Wasi.Consequence.member_sound _ _ (coreBytesInterp_member memberEnv) Γ Δ (member_eq ▸ h)

silmaril instance silmaril.selftest.consequence.wasm_seq.member_complete_within (expect := THM)
  (title := "member_check.wasm (coreInterp) is complete for single-succedent membership within Γ.length + 1 ≤ 2^32 - 1 (nonempty hosts)") :=
  silmaril.shapes.consequence.complete_within_at (S := silmaril.selftest.consequence.wasm_seq.member_check)
  (T := ProjectSelfTest.Consequence.WasmSeq.singleMem)
  (μ := fun (Γ : List UInt8) (_ : List UInt8) => Γ.length + 1) (b := 2 ^ 32 - 1)

@[answers "silmaril.selftest.consequence.wasm_seq.member_complete_within" thm]
public theorem member_complete_within : ∀ Γ Δ,
    CompleteWithinAt silmaril.selftest.consequence.wasm_seq.member_check singleMem
      (fun (Γ : List UInt8) (_ : List UInt8) => Γ.length + 1) (2 ^ 32 - 1) Γ Δ := by
  intro Γ Δ hb hm
  rw [member_eq]
  exact Silmaril.Wasi.Consequence.member_completeOn _ Silmaril.Project.Languages.WasmExport.allHosts_nonempty
    (coreBytesInterp_member memberEnv) Γ Δ (by simp only at hb; omega) hm

-- the two registrations of member_check.wasm agree on single conclusions (coreSeq_single_iff_checkRel)
silmaril instance silmaril.selftest.consequence.wasm_seq.from_check_rel (expect := THM)
  (title := "c ↦ [c] translates member_check.wasm read by check_rel into its coreInterp reading") :=
  silmaril.shapes.consequence.translates_at (S := silmaril.selftest.consequence.wasm.member_check)
  (T := silmaril.selftest.consequence.wasm_seq.member_check) (f := id) (g := fun (c : UInt8) => [c])

@[answers "silmaril.selftest.consequence.wasm_seq.from_check_rel" thm]
public theorem from_check_rel : ∀ Γ c, TranslatesAt silmaril.selftest.consequence.wasm.member_check
    silmaril.selftest.consequence.wasm_seq.member_check id (fun (c : UInt8) => [c]) Γ c := by
  intro Γ c h
  rw [ProjectSelfTest.Consequence.Wasm.member_check_eq] at h
  rw [member_eq]
  exact (Silmaril.Project.ConsequenceSystems.WasmSeq.coreSeq_single_iff_checkRel _ Γ c).2 h

silmaril instance silmaril.selftest.consequence.wasm_seq.to_check_rel (expect := THM)
  (title := "…and reflects it") :=
  silmaril.shapes.consequence.reflects_at (S := silmaril.selftest.consequence.wasm.member_check)
  (T := silmaril.selftest.consequence.wasm_seq.member_check) (f := id) (g := fun (c : UInt8) => [c])

@[answers "silmaril.selftest.consequence.wasm_seq.to_check_rel" thm]
public theorem to_check_rel : ∀ Γ c, ReflectsAt silmaril.selftest.consequence.wasm.member_check
    silmaril.selftest.consequence.wasm_seq.member_check id (fun (c : UInt8) => [c]) Γ c := by
  intro Γ c h
  rw [member_eq] at h
  rw [ProjectSelfTest.Consequence.Wasm.member_check_eq]
  exact (Silmaril.Project.ConsequenceSystems.WasmSeq.coreSeq_single_iff_checkRel _ Γ c).1 h

silmaril instance silmaril.selftest.consequence.wasm_seq.empty_empty (expect := UNS)
  (title := "empty_check.wasm (coreInterp) derives nothing: defined and empty") :=
  silmaril.shapes.consequence.derives (S := silmaril.selftest.consequence.wasm_seq.empty_check)

@[answers "silmaril.selftest.consequence.wasm_seq.empty_empty" uns]
public theorem empty_empty : ∀ Γ Δ, ¬ Derives silmaril.selftest.consequence.wasm_seq.empty_check Γ Δ := by
  intro Γ Δ h
  have hb := coreBytesInterp_empty memberEnv rfl
  have hm : coreBytesInterp memberEnv ⟨Silmaril.Wasm.Examples.EmptyCheck.bytes.toArray⟩ =
      some (coreSeq memberEnv.P memberEnv.Hosts Silmaril.Wasm.Examples.EmptyCheck.prog memberEnv.name memberEnv.enc) := by
    simp [coreBytesInterp, Silmaril.Consequence.Interp.comap, Silmaril.Wasm.Examples.EmptyCheck.decode_bytes, coreInterp]
  rw [empty_eq] at h
  rw [hm] at hb
  exact (Option.some.inj hb ▸ h : (⊥ : System (List UInt8) (List UInt8)) Γ Δ)

end

silmaril group silmaril.selftest.consequence.wasm_seq
  (title := "Registered Wasm artifacts through a partial interpretation (coreInterp)")
  (children := [silmaril.selftest.consequence.wasm_seq.member_defined,
    silmaril.selftest.consequence.wasm_seq.empty_defined,
    silmaril.selftest.consequence.wasm_seq.member_sound,
    silmaril.selftest.consequence.wasm_seq.member_complete_within,
    silmaril.selftest.consequence.wasm_seq.from_check_rel,
    silmaril.selftest.consequence.wasm_seq.to_check_rel,
    silmaril.selftest.consequence.wasm_seq.empty_empty])

silmaril consequence_matrix silmaril.protocols.signed_matrix :=
  Silmaril.Project.ConsequenceSystems.Matrix.signedMatrixRows
