module

public import Silmaril.Project.Shapes.Language.Thms
public import Silmaril.Project.Formats.Wasm.Thms
public import Silmaril.Project.Languages.WasmExport.Thms
public import Silmaril.Wasm.Game.Examples.Defs
public import Silmaril.Formats.JsonBytes.Decide.Thms
public import ProjectSelfTest.Languages

/-!
# The `sil project` self-test: the acceptor modules as registered artifacts

Two core modules of the acceptor interpretation catalog (`Silmaril.Wasi.Accept.Catalog`) are
registered artifacts: `examples/wasm-acceptors/json_accept.wasm`
(`silmaril.wasm.examples.json_accept.prog`) and `examples/wasm-acceptors/ex_start.wasm`
(`silmaril.wasm.game.examples.ex_start`). Their bytes are exactly
`Silmaril.Wasm.Binaryen.Exe.encodeModule?` of the Lean values
`Silmaril.Wasm.Examples.JsonAccept.prog` and `Silmaril.Wasm.Game.Examples.exStart`.

* **Values with certificates** (`@[value]`): each artifact read under `wasm` is one of these
  values. The `.is` problems are solved by `Silmaril.Project.Formats.wasm_is_of_encode`: one
  kernel evaluation of the decoder (`silmaril_decide` on `.parses`) and one of the encoder
  against the bytes. This is the trust boundary between the binary and the AST: the theorems
  are about the AST, and these certificates carry them to the bytes.
* **Languages of the JSON-subset acceptor's bytes** (`op := artifact`) under the export
  interpretations of `Silmaril.Project.Languages.WasmExport`: accepted, rejected, and accepted
  and never rejected. A `decl` language states the subset: integer texts (`intText`) shorter
  than `2 ^ 32` bytes.
* **Claims**, each a restatement of a main theorem (`Silmaril.Wasm.Examples.JsonAccept`):
  equalities with the subset, inclusion in RFC 8259 JSON and its failing converse, and
  membership and non-membership of sentences.

The verified checkers `Examples.EmptyCheck.prog` (`empty_check.wasm`) and
`Examples.MemberCheck.prog` (`member_check.wasm`) are registered the same way. Their languages
are read through the export `check` (`wasm.core.check_accept`, `wasm.core.check_reject`), a
different ABI from `accept`. The claims keep the theorems' assumptions in their titles: the
empty checker accepts nothing at every host set; its rejections, and the membership checker's
exact languages, hold for a nonempty host set (`allHosts`) and inputs shorter than `2 ^ 32`
bytes. Inputs are byte strings, so a "member" is a byte. These are core modules only: no
component wraps them.

`ex_start` gets a certificate only. It calls an import `env.f` with no arguments, so no byte
language is claimed for it.
-/

/-- `examples/wasm-acceptors/json_accept.wasm` is `Examples.JsonAccept.prog`. -/
@[expose, value "silmaril.selftest.wasm_acceptors.json_accept" (format := wasm)
  (source := silmaril.wasm.examples.json_accept.prog)
  (doc := "The verified JSON-subset acceptor (Silmaril.Wasm.Examples.JsonAccept.prog), its encodeModule? bytes")]
public def ProjectSelfTest.WasmAcceptors.jsonAcceptCert : Silmaril.Wasm.Module :=
  Silmaril.Wasm.Examples.JsonAccept.prog

/-- `examples/wasm-acceptors/ex_start.wasm` is `Game.Examples.exStart`. -/
@[expose, value "silmaril.selftest.wasm_acceptors.ex_start" (format := wasm)
  (source := silmaril.wasm.game.examples.ex_start)
  (doc := "A module whose start function calls its import env.f (Silmaril.Wasm.Game.Examples.exStart), its encodeModule? bytes")]
public def ProjectSelfTest.WasmAcceptors.exStartCert : Silmaril.Wasm.Module :=
  Silmaril.Wasm.Game.Examples.exStart

@[solves "silmaril.selftest.wasm_acceptors.json_accept.parses"]
public theorem ProjectSelfTest.WasmAcceptors.json_accept_parses :
    silmaril.selftest.wasm_acceptors.json_accept.parses := by
  silmaril_decide

@[solves "silmaril.selftest.wasm_acceptors.ex_start.parses"]
public theorem ProjectSelfTest.WasmAcceptors.ex_start_parses :
    silmaril.selftest.wasm_acceptors.ex_start.parses := by
  silmaril_decide

@[solves "silmaril.selftest.wasm_acceptors.json_accept.is"]
public theorem ProjectSelfTest.WasmAcceptors.json_accept_is :
    silmaril.selftest.wasm_acceptors.json_accept.is :=
  Silmaril.Project.Formats.wasm_is_of_encode rfl (by decide +kernel)
    ProjectSelfTest.WasmAcceptors.json_accept_parses

@[solves "silmaril.selftest.wasm_acceptors.ex_start.is"]
public theorem ProjectSelfTest.WasmAcceptors.ex_start_is :
    silmaril.selftest.wasm_acceptors.ex_start.is :=
  Silmaril.Project.Formats.wasm_is_of_encode rfl (by decide +kernel)
    ProjectSelfTest.WasmAcceptors.ex_start_parses

/-- `examples/wasm-acceptors/empty_check.wasm` is `Examples.EmptyCheck.prog`. -/
@[expose, value "silmaril.selftest.wasm_acceptors.empty_check" (format := wasm)
  (source := silmaril.wasm.examples.empty_check.prog)
  (doc := "The verified empty checker (Silmaril.Wasm.Examples.EmptyCheck.prog): check(ptr, len) -> i32 answers 0; its encodeModule? bytes")]
public def ProjectSelfTest.WasmAcceptors.emptyCheckCert : Silmaril.Wasm.Module :=
  Silmaril.Wasm.Examples.EmptyCheck.prog

/-- `examples/wasm-acceptors/member_check.wasm` is `Examples.MemberCheck.prog`. -/
@[expose, value "silmaril.selftest.wasm_acceptors.member_check" (format := wasm)
  (source := silmaril.wasm.examples.member_check.prog)
  (doc := "The verified membership checker (Silmaril.Wasm.Examples.MemberCheck.prog): check(ptr, len) -> i32 answers 1 iff the first byte occurs in the rest; its encodeModule? bytes")]
public def ProjectSelfTest.WasmAcceptors.memberCheckCert : Silmaril.Wasm.Module :=
  Silmaril.Wasm.Examples.MemberCheck.prog

@[solves "silmaril.selftest.wasm_acceptors.empty_check.parses"]
public theorem ProjectSelfTest.WasmAcceptors.empty_check_parses :
    silmaril.selftest.wasm_acceptors.empty_check.parses := by
  silmaril_decide

@[solves "silmaril.selftest.wasm_acceptors.member_check.parses"]
public theorem ProjectSelfTest.WasmAcceptors.member_check_parses :
    silmaril.selftest.wasm_acceptors.member_check.parses := by
  silmaril_decide

@[solves "silmaril.selftest.wasm_acceptors.empty_check.is"]
public theorem ProjectSelfTest.WasmAcceptors.empty_check_is :
    silmaril.selftest.wasm_acceptors.empty_check.is :=
  Silmaril.Project.Formats.wasm_is_of_encode rfl (by decide +kernel)
    ProjectSelfTest.WasmAcceptors.empty_check_parses

@[solves "silmaril.selftest.wasm_acceptors.member_check.is"]
public theorem ProjectSelfTest.WasmAcceptors.member_check_is :
    silmaril.selftest.wasm_acceptors.member_check.is :=
  Silmaril.Project.Formats.wasm_is_of_encode rfl (by decide +kernel)
    ProjectSelfTest.WasmAcceptors.member_check_parses

namespace ProjectSelfTest.WasmAcceptors

@[expose] public section

/-- Byte strings whose first byte occurs in the rest (`MemberCheck.memberLang`), shorter than
`2 ^ 32` bytes. -/
def memberBelow : Set (List UInt8) :=
  {w | w ∈ Silmaril.Wasm.Examples.MemberCheck.memberLang ∧ w.length < 2 ^ 32}

/-- Byte strings whose first byte occurs in the rest, of any length. -/
abbrev memberAll : Set (List UInt8) := Silmaril.Wasm.Examples.MemberCheck.memberLang

/-- Integer texts (`ws* -? (0|[1-9][0-9]*) ws*`) shorter than `2 ^ 32` bytes. -/
def intTextBelow : Set (List UInt8) :=
  {w | w ∈ Silmaril.Wasm.Examples.JsonAccept.intText ∧ w.length < 2 ^ 32}

/-- An interpreted artifact with a certificate is the interpretation of the certificate. -/
theorem mem_artifactLang_of_is {V : Type} {X : Silmaril.Project.Value V} {v : V}
    {I : V → Set (List UInt8)} (h : X.Is v) (w : List UInt8) :
    w ∈ Silmaril.Project.Languages.artifactLang X I ↔ w ∈ I v :=
  ⟨fun ⟨_, hv, hw⟩ => (Option.some.inj (h.symm.trans hv)) ▸ hw, fun hw => ⟨v, h, hw⟩⟩

/-- The certificate, at the module the theorems are about. -/
theorem json_accept_is_prog :
    Silmaril.Project.Value.Is silmaril.selftest.wasm_acceptors.json_accept
      Silmaril.Wasm.Examples.JsonAccept.prog :=
  json_accept_is

theorem empty_check_is_prog :
    Silmaril.Project.Value.Is silmaril.selftest.wasm_acceptors.empty_check
      Silmaril.Wasm.Examples.EmptyCheck.prog :=
  empty_check_is

theorem member_check_is_prog :
    Silmaril.Project.Value.Is silmaril.selftest.wasm_acceptors.member_check
      Silmaril.Wasm.Examples.MemberCheck.prog :=
  member_check_is

end

end ProjectSelfTest.WasmAcceptors

silmaril language silmaril.selftest.lang.json_accept.int_text :=
  ProjectSelfTest.WasmAcceptors.intTextBelow (domain := bytes) (op := decl)
  (title := "JSON integer texts shorter than 2^32 bytes")
  (doc := "ws* -? (0|[1-9][0-9]*) ws* (Silmaril.Wasm.Examples.JsonAccept.intText), a subset of RFC 8259 JSON texts, with the export ABI's length bound")

silmaril language silmaril.selftest.lang.json_accept.accepted (domain := bytes) (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.json_accept)
  (interpretation := wasm.core.export_accept)
  (title := "Inputs json_accept.wasm's export accept answers 1 on")
silmaril language silmaril.selftest.lang.json_accept.rejected (domain := bytes) (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.json_accept)
  (interpretation := wasm.core.export_reject)
  (title := "Inputs json_accept.wasm's export accept answers 0 on")
silmaril language silmaril.selftest.lang.json_accept.safe (domain := bytes) (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.json_accept)
  (interpretation := wasm.core.export_accept_safely)
  (title := "Inputs json_accept.wasm accepts and never rejects")

silmaril language silmaril.selftest.lang.member_check.member :=
  ProjectSelfTest.WasmAcceptors.memberAll (domain := bytes) (op := decl)
  (title := "Byte strings whose first byte occurs in the rest")
  (doc := "{w | ∃ c as, w = c :: as ∧ c ∈ as} (Silmaril.Wasm.Examples.MemberCheck.memberLang); bytes, not Unicode")
silmaril language silmaril.selftest.lang.member_check.member_below :=
  ProjectSelfTest.WasmAcceptors.memberBelow (domain := bytes) (op := decl)
  (title := "Byte strings shorter than 2^32 whose first byte occurs in the rest")

silmaril language silmaril.selftest.lang.empty_check.accepted (domain := bytes) (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.empty_check)
  (interpretation := wasm.core.check_accept)
  (title := "Inputs empty_check.wasm's export check answers 1 on")
silmaril language silmaril.selftest.lang.empty_check.rejected (domain := bytes) (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.empty_check)
  (interpretation := wasm.core.check_reject)
  (title := "Inputs empty_check.wasm's export check answers 0 on")
silmaril language silmaril.selftest.lang.member_check.accepted (domain := bytes) (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.member_check)
  (interpretation := wasm.core.check_accept)
  (title := "Inputs member_check.wasm's export check answers 1 on")
silmaril language silmaril.selftest.lang.member_check.rejected (domain := bytes) (op := artifact)
  (value := silmaril.selftest.wasm_acceptors.member_check)
  (interpretation := wasm.core.check_reject)
  (title := "Inputs member_check.wasm's export check answers 0 on")

open ProjectSelfTest.WasmAcceptors Silmaril.Project.Shapes Silmaril.Project.Languages.WasmExport
  Silmaril.Formats in
section

silmaril instance silmaril.selftest.wasm_acceptors.accepted_eq (expect := THM)
  (title := "json_accept.wasm accepts exactly the integer texts below 2^32 bytes") :=
  silmaril.shapes.language.eq_at (L := silmaril.selftest.lang.json_accept.accepted)
  (K := ProjectSelfTest.WasmAcceptors.intTextBelow)

@[answers "silmaril.selftest.wasm_acceptors.accepted_eq" thm]
public theorem accepted_eq :
    ∀ x, EqAt silmaril.selftest.lang.json_accept.accepted intTextBelow x := fun x =>
  (mem_artifactLang_of_is json_accept_is_prog x).trans (Set.ext_iff.mp jsonAccept_exportAccept x)

silmaril instance silmaril.selftest.wasm_acceptors.safe_eq (expect := THM)
  (title := "json_accept.wasm accepts and never rejects exactly the integer texts below 2^32 bytes") :=
  silmaril.shapes.language.eq_at (L := silmaril.selftest.lang.json_accept.safe)
  (K := ProjectSelfTest.WasmAcceptors.intTextBelow)

@[answers "silmaril.selftest.wasm_acceptors.safe_eq" thm]
public theorem safe_eq :
    ∀ x, EqAt silmaril.selftest.lang.json_accept.safe intTextBelow x := fun x =>
  (mem_artifactLang_of_is json_accept_is_prog x).trans
    (Set.ext_iff.mp jsonAccept_exportAcceptSafely x)

silmaril instance silmaril.selftest.wasm_acceptors.accepted_sub_json (expect := THM)
  (title := "What json_accept.wasm accepts is JSON (RFC 8259)") :=
  silmaril.shapes.language.subset_at (L := silmaril.selftest.lang.json_accept.accepted)
  (K := ProjectSelfTest.Languages.jsonRfc8259)

@[answers "silmaril.selftest.wasm_acceptors.accepted_sub_json" thm]
public theorem accepted_sub_json :
    ∀ x, SubsetAt silmaril.selftest.lang.json_accept.accepted
      ProjectSelfTest.Languages.jsonRfc8259 x := fun x hx =>
  Silmaril.Wasm.Examples.JsonAccept.exportAccepted_subset_json _ _ _
    ((mem_artifactLang_of_is json_accept_is_prog x).1 hx)

-- the converse fails: `[]` is a JSON text but not an integer text
silmaril instance silmaril.selftest.wasm_acceptors.json_sub_accepted (expect := CSA)
  (title := "JSON ⊆ what json_accept.wasm accepts (fails: [])") :=
  silmaril.shapes.language.subset_at (L := ProjectSelfTest.Languages.jsonRfc8259)
  (K := silmaril.selftest.lang.json_accept.accepted)

@[answers "silmaril.selftest.wasm_acceptors.json_sub_accepted" csa]
public theorem json_sub_accepted :
    ∃ x, ¬ SubsetAt ProjectSelfTest.Languages.jsonRfc8259
      silmaril.selftest.lang.json_accept.accepted x :=
  ⟨[0x5B, 0x5D], fun h => absurd ((Silmaril.Wasm.Examples.JsonAccept.acc_iff _).2
      ((accepted_eq _).1 (h (JsonBytes.Decide.textB_iff.mp (by decide)))).1) (by decide)⟩

silmaril instance silmaril.selftest.wasm_acceptors.accepts_one (expect := THM)
  (title := "json_accept.wasm accepts `1`") :=
  silmaril.shapes.language.member (L := silmaril.selftest.lang.json_accept.accepted) (x := [0x31])

@[answers "silmaril.selftest.wasm_acceptors.accepts_one" thm]
public theorem accepts_one : Member silmaril.selftest.lang.json_accept.accepted [0x31] :=
  (accepted_eq _).2 (And.intro ((Silmaril.Wasm.Examples.JsonAccept.acc_iff _).1 (by decide))
    (by decide))

silmaril instance silmaril.selftest.wasm_acceptors.rejects_one (expect := UNS)
  (title := "json_accept.wasm rejects `1` (fails: no run answers 0)") :=
  silmaril.shapes.language.member (L := silmaril.selftest.lang.json_accept.rejected) (x := [0x31])

@[answers "silmaril.selftest.wasm_acceptors.rejects_one" csa]
public theorem rejects_one : ¬ Member silmaril.selftest.lang.json_accept.rejected [0x31] :=
  fun h => ((Set.ext_iff.mp jsonAccept_exportReject _).1
    ((mem_artifactLang_of_is json_accept_is_prog _).1 h)).1
    ((Silmaril.Wasm.Examples.JsonAccept.acc_iff _).1 (by decide))

silmaril instance silmaril.selftest.wasm_acceptors.rejects_brackets (expect := THM)
  (title := "json_accept.wasm rejects `[]` (JSON, outside the subset)") :=
  silmaril.shapes.language.member (L := silmaril.selftest.lang.json_accept.rejected)
  (x := [0x5B, 0x5D])

@[answers "silmaril.selftest.wasm_acceptors.rejects_brackets" thm]
public theorem rejects_brackets :
    Member silmaril.selftest.lang.json_accept.rejected [0x5B, 0x5D] :=
  (mem_artifactLang_of_is json_accept_is_prog _).2 ((Set.ext_iff.mp jsonAccept_exportReject _).2
    (And.intro (fun h => absurd ((Silmaril.Wasm.Examples.JsonAccept.acc_iff _).2 h) (by decide))
      (by decide)))

-- the checkers: assumptions are in the titles
silmaril instance silmaril.selftest.wasm_acceptors.empty_accepts_nothing (expect := UNS)
  (title := "empty_check.wasm accepts something (fails: nothing, at every host set)") :=
  silmaril.shapes.language.member (L := silmaril.selftest.lang.empty_check.accepted)

@[answers "silmaril.selftest.wasm_acceptors.empty_accepts_nothing" uns]
public theorem empty_accepts_nothing :
    ∀ x, ¬ Member silmaril.selftest.lang.empty_check.accepted x := fun x h => by
  have h' := (mem_artifactLang_of_is empty_check_is_prog x).1 h
  rw [emptyCheck_checkAccept] at h'
  exact h'

silmaril instance silmaril.selftest.wasm_acceptors.empty_rejects_nil (expect := THM)
  (title := "empty_check.wasm rejects the empty input (nonempty host set, < 2^32 bytes)") :=
  silmaril.shapes.language.member (L := silmaril.selftest.lang.empty_check.rejected) (x := [])

@[answers "silmaril.selftest.wasm_acceptors.empty_rejects_nil" thm]
public theorem empty_rejects_nil : Member silmaril.selftest.lang.empty_check.rejected [] :=
  (mem_artifactLang_of_is empty_check_is_prog _).2
    ((Set.ext_iff.mp emptyCheck_checkReject _).2 (by decide))

silmaril instance silmaril.selftest.wasm_acceptors.member_accepted_sub (expect := THM)
  (title := "What member_check.wasm accepts has its first byte in the rest (every host set)") :=
  silmaril.shapes.language.subset_at (L := silmaril.selftest.lang.member_check.accepted)
  (K := ProjectSelfTest.WasmAcceptors.memberAll)

@[answers "silmaril.selftest.wasm_acceptors.member_accepted_sub" thm]
public theorem member_accepted_sub :
    ∀ x, SubsetAt silmaril.selftest.lang.member_check.accepted memberAll x := fun x hx =>
  memberCheck_checkAccept_subset ((mem_artifactLang_of_is member_check_is_prog x).1 hx)

silmaril instance silmaril.selftest.wasm_acceptors.member_accepted_eq (expect := THM)
  (title := "member_check.wasm accepts exactly the member strings below 2^32 bytes (nonempty host set)") :=
  silmaril.shapes.language.eq_at (L := silmaril.selftest.lang.member_check.accepted)
  (K := ProjectSelfTest.WasmAcceptors.memberBelow)

@[answers "silmaril.selftest.wasm_acceptors.member_accepted_eq" thm]
public theorem member_accepted_eq :
    ∀ x, EqAt silmaril.selftest.lang.member_check.accepted memberBelow x := fun x =>
  (mem_artifactLang_of_is member_check_is_prog x).trans (Set.ext_iff.mp memberCheck_checkAccept x)

silmaril instance silmaril.selftest.wasm_acceptors.member_accepts_aa (expect := THM)
  (title := "member_check.wasm accepts the bytes 61 61 (`a` occurs in `a`)") :=
  silmaril.shapes.language.member (L := silmaril.selftest.lang.member_check.accepted)
  (x := [0x61, 0x61])

@[answers "silmaril.selftest.wasm_acceptors.member_accepts_aa" thm]
public theorem member_accepts_aa :
    Member silmaril.selftest.lang.member_check.accepted [0x61, 0x61] :=
  (member_accepted_eq _).2 (And.intro (by decide) (by decide))

silmaril instance silmaril.selftest.wasm_acceptors.member_accepts_ab (expect := UNS)
  (title := "member_check.wasm accepts the bytes 61 62 (fails: `a` does not occur in `b`)") :=
  silmaril.shapes.language.member (L := silmaril.selftest.lang.member_check.accepted)
  (x := [0x61, 0x62])

@[answers "silmaril.selftest.wasm_acceptors.member_accepts_ab" csa]
public theorem member_accepts_ab :
    ¬ Member silmaril.selftest.lang.member_check.accepted [0x61, 0x62] := fun h =>
  absurd (show [0x61, 0x62] ∈ Silmaril.Wasm.Examples.MemberCheck.memberLang from
    member_accepted_sub _ h) (by decide)

silmaril instance silmaril.selftest.wasm_acceptors.member_rejects_ab (expect := THM)
  (title := "member_check.wasm rejects the bytes 61 62 (nonempty host set, < 2^32 bytes)") :=
  silmaril.shapes.language.member (L := silmaril.selftest.lang.member_check.rejected)
  (x := [0x61, 0x62])

@[answers "silmaril.selftest.wasm_acceptors.member_rejects_ab" thm]
public theorem member_rejects_ab :
    Member silmaril.selftest.lang.member_check.rejected [0x61, 0x62] :=
  (mem_artifactLang_of_is member_check_is_prog _).2
    ((Set.ext_iff.mp memberCheck_checkReject _).2 (And.intro (by decide) (by decide)))

end

silmaril group silmaril.selftest.wasm_acceptors (title := "Acceptor modules as registered artifacts")
  (children := [silmaril.selftest.wasm_acceptors.json_accept.is,
    silmaril.selftest.wasm_acceptors.json_accept.parses,
    silmaril.selftest.wasm_acceptors.ex_start.is, silmaril.selftest.wasm_acceptors.ex_start.parses,
    silmaril.selftest.wasm_acceptors.accepted_eq, silmaril.selftest.wasm_acceptors.safe_eq,
    silmaril.selftest.wasm_acceptors.accepted_sub_json,
    silmaril.selftest.wasm_acceptors.json_sub_accepted,
    silmaril.selftest.wasm_acceptors.accepts_one, silmaril.selftest.wasm_acceptors.rejects_one,
    silmaril.selftest.wasm_acceptors.rejects_brackets,
    silmaril.selftest.wasm_acceptors.empty_check.is,
    silmaril.selftest.wasm_acceptors.empty_check.parses,
    silmaril.selftest.wasm_acceptors.member_check.is,
    silmaril.selftest.wasm_acceptors.member_check.parses,
    silmaril.selftest.wasm_acceptors.empty_accepts_nothing,
    silmaril.selftest.wasm_acceptors.empty_rejects_nil,
    silmaril.selftest.wasm_acceptors.member_accepted_sub,
    silmaril.selftest.wasm_acceptors.member_accepted_eq,
    silmaril.selftest.wasm_acceptors.member_accepts_aa,
    silmaril.selftest.wasm_acceptors.member_accepts_ab,
    silmaril.selftest.wasm_acceptors.member_rejects_ab])
