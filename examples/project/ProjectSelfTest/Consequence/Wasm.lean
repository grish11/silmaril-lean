module

public import Silmaril.Project.ConsequenceSystems.WasmExport.Defs
public import Silmaril.Project.Shapes.Consequence.Thms
public import Silmaril.Wasm.Examples.MemberCheck.Thms
public import Silmaril.Wasm.Examples.EmptyCheck.Thms
public import ProjectSelfTest.WasmAcceptors

/-!
# The `sil project` self-test: consequence systems of registered Wasm artifacts

The registered checkers `examples/wasm-acceptors/member_check.wasm` (108 bytes) and
`empty_check.wasm` (45 bytes) (`ProjectSelfTest.WasmAcceptors`) as consequence systems
(`op := artifact`) under `wasm.core.check_rel`: `as ⊢ c` iff some run of the export
`check(ptr: i32, len: i32) -> i32` answers `1` on the bytes `c :: as`, `Profile.spec`, every
Core host. Statements and assumptions are single bytes (`UInt8`); no component wraps either
module.

* The values' `.is` problems (kernel-checked decode certificates, in `WasmAcceptors`) tie each
  artifact to its Lean module, so the artifact's system **equals** the module's relation:
  `member_check` is `MemberCheck.accepted Profile.spec allHosts` (sound and complete for each
  other, both THM).
* With the length bound of the export ABI: `member_check` is exactly membership of the
  conclusion in the assumptions **for assumption lists of fewer than `2 ^ 32 - 1` bytes**
  (`mem_below`). Both directions use a nonempty host set (`allHosts`): soundness through the
  global bound of `MemberCheck.exportAccepted_eq`, completeness through `accepted_iff_mem`.
* Member judgments: `1, 2 ⊢ 2` holds, `1 ⊢ 2` does not.
* `empty_check` derives nothing (`EmptyCheck.exportAccepted_eq_empty`, every profile and host
  set). Its bytes do decode (its `.is` certificate): this is a verified checker that accepts
  nothing, not a decode failure.
-/

namespace ProjectSelfTest.Consequence.Wasm

open Silmaril.Project.ConsequenceSystems Silmaril.Project.Languages.WasmExport

@[expose] public section

/-- The module's relation, as the protocol track states it. -/
def memberAccepted : Silmaril.Consequence.System (List UInt8) UInt8 :=
  Silmaril.Wasm.Examples.MemberCheck.accepted Silmaril.Wasm.Numerics.Profile.spec allHosts

/-- Membership of the conclusion in the assumptions, unbounded. -/
def memAll : Silmaril.Consequence.System (List UInt8) UInt8 := fun as c => c ∈ as

/-- Membership, for assumption lists that fit the ABI with the conclusion: `as.length + 1 < 2 ^ 32`. -/
def memBelow : Silmaril.Consequence.System (List UInt8) UInt8 :=
  fun as c => c ∈ as ∧ as.length + 1 < 2 ^ 32

/-- The registered language `silmaril.selftest.lang.member_check.accepted` (an artifact language
of the same value), as an acceptor with unit contexts. -/
def acceptedLang : Silmaril.Consequence.System Unit (List UInt8) :=
  Silmaril.Consequence.liftTTC () silmaril.selftest.lang.member_check.accepted

end

end ProjectSelfTest.Consequence.Wasm

silmaril consequence_system silmaril.selftest.consequence.wasm.member_check (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.member_check) (interpretation := wasm.core.check_rel)
  (title := "member_check.wasm through its export check (bytes; Profile.spec, every host)")
silmaril consequence_system silmaril.selftest.consequence.wasm.empty_check (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.empty_check) (interpretation := wasm.core.check_rel)
  (title := "empty_check.wasm through its export check (bytes; Profile.spec, every host)")
silmaril consequence_system silmaril.selftest.consequence.wasm.member_accepted :=
  ProjectSelfTest.Consequence.Wasm.memberAccepted
  (title := "MemberCheck.accepted Profile.spec allHosts: the Lean module's relation")
silmaril consequence_system silmaril.selftest.consequence.wasm.mem_all :=
  ProjectSelfTest.Consequence.Wasm.memAll (title := "c ∈ as (bytes, no bound)")
silmaril consequence_system silmaril.selftest.consequence.wasm.mem_below :=
  ProjectSelfTest.Consequence.Wasm.memBelow
  (title := "c ∈ as, for as.length + 1 < 2^32 (bytes)")

silmaril consequence_system silmaril.selftest.consequence.wasm.member_check.acceptor (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.member_check) (interpretation := wasm.core.check_acceptor)
  (title := "member_check.wasm as an acceptor: () ⊢ w iff check answers 1 on w")
silmaril consequence_system silmaril.selftest.consequence.wasm.member_check.rejector (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.member_check) (interpretation := wasm.core.check_rejector)
  (title := "member_check.wasm as a rejector: w ⊢ () iff check answers 0 on w")
silmaril consequence_system silmaril.selftest.consequence.wasm.member_check.accepted_lang :=
  ProjectSelfTest.Consequence.Wasm.acceptedLang
  (title := "liftTTC () of the registered language silmaril.selftest.lang.member_check.accepted")

namespace ProjectSelfTest.Consequence.Wasm

open Silmaril.Project.ConsequenceSystems Silmaril.Project.Languages.WasmExport
  Silmaril.Project.Shapes.Consequence

/-- The registered artifact's system is the Lean module's relation (its `.is` certificate). -/
public theorem member_check_eq : silmaril.selftest.consequence.wasm.member_check = memberAccepted :=
  artifactSystem_of_is ProjectSelfTest.WasmAcceptors.member_check_is_prog

public theorem empty_check_eq : silmaril.selftest.consequence.wasm.empty_check =
    WasmExport.checkRel Silmaril.Wasm.Examples.EmptyCheck.prog :=
  artifactSystem_of_is ProjectSelfTest.WasmAcceptors.empty_check_is_prog

end ProjectSelfTest.Consequence.Wasm

open ProjectSelfTest.Consequence.Wasm Silmaril.Project.ConsequenceSystems
  Silmaril.Project.Languages.WasmExport Silmaril.Project.Shapes.Consequence in
section

silmaril instance silmaril.selftest.consequence.wasm.member_check_sound_lean (expect := THM)
  (title := "member_check.wasm ⊆ MemberCheck.accepted (by the .is certificate)") :=
  silmaril.shapes.consequence.sound_at (S := silmaril.selftest.consequence.wasm.member_check)
  (T := ProjectSelfTest.Consequence.Wasm.memberAccepted)

@[answers "silmaril.selftest.consequence.wasm.member_check_sound_lean" thm]
public theorem member_check_sound_lean : ∀ Γ φ,
    SoundAt silmaril.selftest.consequence.wasm.member_check memberAccepted Γ φ :=
  fun _ _ h => member_check_eq ▸ h

silmaril instance silmaril.selftest.consequence.wasm.member_check_complete_lean (expect := THM)
  (title := "MemberCheck.accepted ⊆ member_check.wasm (by the .is certificate)") :=
  silmaril.shapes.consequence.complete_at (S := silmaril.selftest.consequence.wasm.member_check)
  (T := ProjectSelfTest.Consequence.Wasm.memberAccepted)

@[answers "silmaril.selftest.consequence.wasm.member_check_complete_lean" thm]
public theorem member_check_complete_lean : ∀ Γ φ,
    CompleteAt silmaril.selftest.consequence.wasm.member_check memberAccepted Γ φ :=
  fun _ _ h => member_check_eq ▸ h

silmaril instance silmaril.selftest.consequence.wasm.member_check_sound_mem (expect := THM)
  (title := "member_check.wasm derives only c ∈ as, with as.length + 1 < 2^32 (nonempty hosts)") :=
  silmaril.shapes.consequence.sound_at (S := silmaril.selftest.consequence.wasm.member_check)
  (T := ProjectSelfTest.Consequence.Wasm.memBelow)

@[answers "silmaril.selftest.consequence.wasm.member_check_sound_mem" thm]
public theorem member_check_sound_mem : ∀ Γ φ,
    SoundAt silmaril.selftest.consequence.wasm.member_check memBelow Γ φ := by
  intro as c h
  rw [member_check_eq] at h
  have h' : c :: as ∈ {w | w ∈ Silmaril.Wasm.Examples.MemberCheck.memberLang ∧ w.length < 2 ^ 32} :=
    Silmaril.Wasm.Examples.MemberCheck.exportAccepted_eq _ allHosts_nonempty ▸ h
  obtain ⟨⟨c', as', he, hm⟩, hl⟩ := h'
  cases he
  exact ⟨hm, by simpa using hl⟩

silmaril instance silmaril.selftest.consequence.wasm.member_check_complete_mem (expect := THM)
  (title := "member_check.wasm derives every c ∈ as with as.length + 1 < 2^32 (nonempty hosts)") :=
  silmaril.shapes.consequence.complete_at (S := silmaril.selftest.consequence.wasm.member_check)
  (T := ProjectSelfTest.Consequence.Wasm.memBelow)

@[answers "silmaril.selftest.consequence.wasm.member_check_complete_mem" thm]
public theorem member_check_complete_mem : ∀ Γ φ,
    CompleteAt silmaril.selftest.consequence.wasm.member_check memBelow Γ φ := by
  intro as c ⟨hm, hl⟩
  rw [member_check_eq]
  exact (Silmaril.Wasm.Examples.MemberCheck.accepted_iff_mem _ allHosts_nonempty hl c).2 hm

silmaril instance silmaril.selftest.consequence.wasm.member_check_complete_within (expect := THM)
  (title := "member_check.wasm is complete for MemberCheck's c ∈ as within as.length + 1 ≤ 2^32 - 1 (nonempty hosts)") :=
  silmaril.shapes.consequence.complete_within_at (S := silmaril.selftest.consequence.wasm.member_check)
  (T := ProjectSelfTest.Consequence.Wasm.memAll)
  (μ := fun (as : List UInt8) (_ : UInt8) => as.length + 1) (b := 2 ^ 32 - 1)

@[answers "silmaril.selftest.consequence.wasm.member_check_complete_within" thm]
public theorem member_check_complete_within : ∀ Γ φ,
    CompleteWithinAt silmaril.selftest.consequence.wasm.member_check memAll
      (fun (as : List UInt8) (_ : UInt8) => as.length + 1) (2 ^ 32 - 1) Γ φ := by
  intro as c hb hm
  exact member_check_complete_mem as c ⟨hm, by simp only at hb; omega⟩

-- the acceptor is the registered language, as a system; the rejector rejects [1]
silmaril instance silmaril.selftest.consequence.wasm.acceptor_is_language (expect := THM)
  (title := "member_check.wasm's acceptor ⊆ its registered language (as liftTTC ())") :=
  silmaril.shapes.consequence.sound_at (S := silmaril.selftest.consequence.wasm.member_check.acceptor)
  (T := ProjectSelfTest.Consequence.Wasm.acceptedLang)

@[answers "silmaril.selftest.consequence.wasm.acceptor_is_language" thm]
public theorem acceptor_is_language : ∀ Γ φ, SoundAt silmaril.selftest.consequence.wasm.member_check.acceptor
    acceptedLang Γ φ := by
  intro u w h
  rw [show silmaril.selftest.consequence.wasm.member_check.acceptor =
    Silmaril.Project.ConsequenceSystems.WasmExport.checkAcceptor Silmaril.Wasm.Examples.MemberCheck.prog from
      artifactSystem_of_is ProjectSelfTest.WasmAcceptors.member_check_is_prog] at h
  exact ⟨h.1, (ProjectSelfTest.WasmAcceptors.mem_artifactLang_of_is
    ProjectSelfTest.WasmAcceptors.member_check_is_prog w).2 h.2⟩

silmaril instance silmaril.selftest.consequence.wasm.language_is_acceptor (expect := THM)
  (title := "member_check.wasm's registered language (as liftTTC ()) ⊆ its acceptor") :=
  silmaril.shapes.consequence.complete_at (S := silmaril.selftest.consequence.wasm.member_check.acceptor)
  (T := ProjectSelfTest.Consequence.Wasm.acceptedLang)

@[answers "silmaril.selftest.consequence.wasm.language_is_acceptor" thm]
public theorem language_is_acceptor : ∀ Γ φ, CompleteAt silmaril.selftest.consequence.wasm.member_check.acceptor
    acceptedLang Γ φ := by
  intro u w h
  rw [show silmaril.selftest.consequence.wasm.member_check.acceptor =
    Silmaril.Project.ConsequenceSystems.WasmExport.checkAcceptor Silmaril.Wasm.Examples.MemberCheck.prog from
      artifactSystem_of_is ProjectSelfTest.WasmAcceptors.member_check_is_prog]
  exact ⟨h.1, (ProjectSelfTest.WasmAcceptors.mem_artifactLang_of_is
    ProjectSelfTest.WasmAcceptors.member_check_is_prog w).1 h.2⟩

silmaril instance silmaril.selftest.consequence.wasm.acceptor_212 (expect := THM)
  (title := "() ⊢ [2, 1, 2]: member_check.wasm accepts 2, 1, 2") := silmaril.shapes.consequence.derives
  (S := silmaril.selftest.consequence.wasm.member_check.acceptor) (Γ := ()) (φ := [2, 1, 2])

@[answers "silmaril.selftest.consequence.wasm.acceptor_212" thm]
public theorem acceptor_212 : Derives silmaril.selftest.consequence.wasm.member_check.acceptor () [2, 1, 2] := by
  rw [show silmaril.selftest.consequence.wasm.member_check.acceptor =
    Silmaril.Project.ConsequenceSystems.WasmExport.checkAcceptor Silmaril.Wasm.Examples.MemberCheck.prog from
      artifactSystem_of_is ProjectSelfTest.WasmAcceptors.member_check_is_prog]
  refine ⟨rfl, ?_⟩
  show [2, 1, 2] ∈ checkAccept Silmaril.Wasm.Examples.MemberCheck.prog
  rw [memberCheck_checkAccept]
  exact ⟨⟨2, [1, 2], rfl, by decide⟩, by decide⟩

silmaril instance silmaril.selftest.consequence.wasm.rejector_1 (expect := THM)
  (title := "[1] ⊢ (): member_check.wasm rejects 1 (nonempty hosts)") := silmaril.shapes.consequence.derives
  (S := silmaril.selftest.consequence.wasm.member_check.rejector) (Γ := [1]) (φ := ())

@[answers "silmaril.selftest.consequence.wasm.rejector_1" thm]
public theorem rejector_1 : Derives silmaril.selftest.consequence.wasm.member_check.rejector [1] () := by
  rw [show silmaril.selftest.consequence.wasm.member_check.rejector =
    Silmaril.Project.ConsequenceSystems.WasmExport.checkRejector Silmaril.Wasm.Examples.MemberCheck.prog from
      artifactSystem_of_is ProjectSelfTest.WasmAcceptors.member_check_is_prog]
  refine ⟨?_, rfl⟩
  show [1] ∈ checkReject Silmaril.Wasm.Examples.MemberCheck.prog
  rw [memberCheck_checkReject]
  exact ⟨fun ⟨_, _, h, hm⟩ => by cases h; simp at hm, by decide⟩

silmaril instance silmaril.selftest.consequence.wasm.member_check_12_2 (expect := THM)
  (title := "1, 2 ⊢ 2 in member_check.wasm") := silmaril.shapes.consequence.derives
  (S := silmaril.selftest.consequence.wasm.member_check) (Γ := [1, 2]) (φ := 2)

@[answers "silmaril.selftest.consequence.wasm.member_check_12_2" thm]
public theorem member_check_12_2 :
    Derives silmaril.selftest.consequence.wasm.member_check [1, 2] 2 :=
  member_check_complete_mem _ _ ⟨by decide, by decide⟩

silmaril instance silmaril.selftest.consequence.wasm.member_check_1_2 (expect := UNS)
  (title := "1 ⊢ 2 in member_check.wasm (fails)") := silmaril.shapes.consequence.derives
  (S := silmaril.selftest.consequence.wasm.member_check) (Γ := [1]) (φ := 2)

@[answers "silmaril.selftest.consequence.wasm.member_check_1_2" csa]
public theorem member_check_1_2 :
    ¬ Derives silmaril.selftest.consequence.wasm.member_check [1] 2 :=
  fun h => absurd (member_check_sound_mem _ _ h).1 (by decide)

silmaril instance silmaril.selftest.consequence.wasm.empty_check_empty (expect := UNS)
  (title := "empty_check.wasm derives nothing (decodes: a verified empty checker, every host set)") :=
  silmaril.shapes.consequence.derives (S := silmaril.selftest.consequence.wasm.empty_check)

@[answers "silmaril.selftest.consequence.wasm.empty_check_empty" uns]
public theorem empty_check_empty :
    ∀ Γ φ, ¬ Derives silmaril.selftest.consequence.wasm.empty_check Γ φ := by
  intro as c h
  rw [empty_check_eq] at h
  exact (Silmaril.Wasm.Examples.EmptyCheck.exportAccepted_eq_empty _ _ ▸ h : c :: as ∈ (∅ : Set (List UInt8)))

end

silmaril group silmaril.selftest.consequence.wasm
  (title := "Consequence systems of registered Wasm artifacts (export check)")
  (children := [silmaril.selftest.consequence.wasm.member_check_sound_lean,
    silmaril.selftest.consequence.wasm.member_check_complete_lean,
    silmaril.selftest.consequence.wasm.member_check_sound_mem,
    silmaril.selftest.consequence.wasm.member_check_complete_mem,
    silmaril.selftest.consequence.wasm.member_check_complete_within,
    silmaril.selftest.consequence.wasm.acceptor_is_language,
    silmaril.selftest.consequence.wasm.language_is_acceptor,
    silmaril.selftest.consequence.wasm.acceptor_212, silmaril.selftest.consequence.wasm.rejector_1,
    silmaril.selftest.consequence.wasm.member_check_12_2,
    silmaril.selftest.consequence.wasm.member_check_1_2,
    silmaril.selftest.consequence.wasm.empty_check_empty])
