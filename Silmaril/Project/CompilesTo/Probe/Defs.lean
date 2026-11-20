module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Codec.File.Defs

/-!
# Probe: the Core elaboration of a C text, as a canonical document

`docText text` runs the Lean Cerberus frontend (`FrontendAil`) and elaborator (`ElabAil`) on
`text` and prints the typed Ail (the text `ail_program%` reads) and the Core, a canonical `cerb-export` document (`Codec.encodeDocument`, `printTagged`), the text
that `core_document%` (`Silmaril.Cerberus.Core.Quote`) turns back into a `Codec.Document` literal.
`tools/c-tv` runs it at elaboration time (`run_cmd logWarning …` in a scratch module, with
`meta import` of this module) and reads the document between the markers. The output is
untrusted: a generated header states `ElaboratesTo` about the quoted literal, and Lean checks it.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo.Probe

open Silmaril.Cerberus
open Silmaril.Project.Shapes.C (FrontendAil ElabAil)

/-- The commit field of the probe's documents. -/
def commit : String := "silmaril-lean Lean Cerberus port (Project.Shapes.C.ElabAil)"

/-- The implementation field of the probe's documents. -/
def implementation : String :=
  "TargetCoherence.linuxLP64; ParameterCallReturn.Example.runtime (constructed)"

/-- The canonical document of the elaborated bindings. -/
def document (b : Codec.FileBindings) : String :=
  Silmaril.Formats.SExpEncoding.printTagged
    (Codec.encodeDocument ⟨commit, implementation, b, b.toFile, rfl, none⟩) ++ "\n"

/-- The canonical wire text of a typed Ail program (what `ail_program%` reads). -/
def ailText (p : Ail.TypedProgram) : String :=
  Ail.Codec.emitProgram Ail.Codec.emitGenTypeCategory p ""

/-- Serialize the typed Ail and Core supplied to a model, in the probe's wire format. -/
def modelText (ail : Ail.TypedProgram) (core : Codec.FileBindings) : String :=
  "BEGIN-TYPED-AIL\n" ++ ailText ail ++ "\nEND-TYPED-AIL\nBEGIN-CORE-DOCUMENT\n" ++
    document core ++ "END-CORE-DOCUMENT\n"

/-- Display a proved decoder listing. Offsets are relative to the function, not the ELF file. -/
def listingText (listing : List (Nat × Silmaril.X86.Ext.Instr × Nat)) (decl : String) : String :=
  s!"-- {decl}: the decoder's listing, checked by the kernel (decodesAs)\n" ++
  "-- offset, length, instruction (Repr, with Silmaril.X86.Ext. and Silmaril.X86. dropped)\n" ++
  String.join (listing.map fun (off, instr, len) =>
    let text := (((repr instr).pretty 400).replace "Silmaril.X86.Ext." "").replace "Silmaril.X86." ""
    s!"0x{String.ofList (Nat.toDigits 16 off)}\t{len}\t{text}\n")

/-- **The probe**: the typed Ail of the C text between `BEGIN-TYPED-AIL`/`END-TYPED-AIL`, then
its Core between `BEGIN-CORE-DOCUMENT`/`END-CORE-DOCUMENT`; or `FRONTEND-ERROR: …`,
`CORE-ELAB-ERROR: …`. -/
def docText (text : String) : String :=
  match FrontendAil text with
  | .error e => "FRONTEND-ERROR: " ++ e
  | .ok ail =>
    "BEGIN-TYPED-AIL\n" ++ ailText ail ++ "\nEND-TYPED-AIL\n" ++
    match ElabAil ail with
    | .ok b => "BEGIN-CORE-DOCUMENT\n" ++ document b ++ "END-CORE-DOCUMENT"
    | .error e => "CORE-ELAB-ERROR: " ++ (reprStr e)

end Silmaril.Project.CompilesTo.Probe

end
