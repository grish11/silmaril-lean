import CompilesToExamples.Straight.Defs
import CompilesToExamples.Branch.Defs
import Silmaril.Project.CompilesTo.Probe.Defs

/-!
# The trusted disassembly stage's exact output, as text

    lake env lean --run tools/compiler-explorer/decoded_listing.lean OUTDIR

Prints each compiles-to function's listing, the `List (offset × Instr × length)` that the header
proves is the decoding of the function's bytes (`<f>_decodes : decodesAs code 0 listing = true`,
by `decide +kernel`), one instruction per line, as `Repr` writes the Lean term. The text is a
rendering of that Lean value; the kernel checked the value, not this file.
-/

def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "usage: OUTDIR")
  for (name, l, decl) in [
      ("straight/O0", CompilesToExamples.Straight.O0.add3Listing, "CompilesToExamples.Straight.O0.add3Listing"),
      ("straight/O2", CompilesToExamples.Straight.O2.add3Listing, "CompilesToExamples.Straight.O2.add3Listing"),
      ("branch/O0", CompilesToExamples.Branch.O0.max2Listing, "CompilesToExamples.Branch.O0.max2Listing"),
      ("branch/O2", CompilesToExamples.Branch.O2.max2Listing, "CompilesToExamples.Branch.O2.max2Listing")] do
    IO.FS.writeFile s!"{dir}/{name}/decoded.txt" (Silmaril.Project.CompilesTo.Probe.listingText l decl)
