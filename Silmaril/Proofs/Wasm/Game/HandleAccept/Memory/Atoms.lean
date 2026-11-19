module

public import Silmaril.Wasm.Game.HandleAccept.Memory.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Thms
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.Basic

/-!
# Proofs: without a `sexp` import, only atoms

`memWriterLang_subset_atoms`: a module none of whose imports is the `sexp` import accepts only
atoms through memory-carrying writer imports (every input tag is decoded from a callout of an
import of the module, `tsession_inputs`; a write is then an atom write, `memWrite_cases`).

New proofs (no source).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Memory

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Writers
  Silmaril.Wasm.Game.HandleAccept.Memory

/-- **Without a `sexp` import a module accepts only atoms.** -/
theorem memWriterLang_subset_atoms {P : Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : MemImports} {pol : Policy (BitVec 32)}
    (hs : ∀ i ∈ m.imports, (i.moduleName, i.name) ≠ ix.sexp) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P Envs memIdx m ix pol ⊆ {x | ∃ a, x = .atom a} := by
  refine writerLang_subset_of_closed ha hw ?_
  rintro _ ⟨ts, ⟨_, _, _, -, _, _, -, _, _, _, hts⟩, rfl⟩ op args r hm
  have hi := (mem_inputsOf hm).resolve_right (by simp)
  obtain ⟨o, ⟨c, hc⟩, hd | ⟨wr, hd⟩⟩ := tsession_inputs hts _ hi
  · exact absurd hd memAccept_not_write
  · rcases memWrite_cases hd with he | ⟨a, rfl, rfl⟩
    · obtain ⟨i, hi, hio⟩ := calloutAt?_imp hc
      exact absurd (hio ▸ he) (hs i hi)
    · intro cs y _ hb _
      cases cs with
      | nil => cases hb; exact ⟨a, rfl⟩
      | cons _ _ => cases hb

end Silmaril.Proofs.Wasm.Game.HandleAccept.Memory
