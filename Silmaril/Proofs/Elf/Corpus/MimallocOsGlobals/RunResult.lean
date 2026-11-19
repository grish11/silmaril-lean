module
public import Silmaril.Elf.Corpus.MimallocOsGlobals.Source.Elaboration.Defs
namespace Silmaril.Proofs.Elf.Corpus.MimallocOsGlobals
open Silmaril.Elf.Corpus.MimallocOsGlobals.Source
public theorem run_eq_core : inputs.run ail = .ok Elaboration.core := by
  have success := Elaboration.succeeds
  cases h : inputs.run ail with
  | error error =>
    rw [h] at success
    change false = true at success
    contradiction
  | ok bindings =>
    simp only [Elaboration.core, h]
    rfl
end Silmaril.Proofs.Elf.Corpus.MimallocOsGlobals
