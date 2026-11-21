module

public import Silmaril.Wasm.Game.HandleAccept.Memory.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.Basic
import Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.Atoms

/-!
# Memory-carrying writer imports: laws

* `inp_of_tsession`: every input tag of a traced session is decoded from a callout of an
  import **of the module** (`calloutAt?`), at its call (`callIn`) or at an answer to it
  (`answerIn`);
* `memWriterLang_subset_atoms`: a module none of whose imports is the `sexp` import accepts only
  atoms through memory-carrying writer imports, for every profile, environment class, memory
  index and policy without UB (no obligation).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Memory

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Writers

theorem inp_of_tsession {X I O C : Type} {P : Profile} {L : SEnv UImp} {m : Module}
    {memAddr : Option Nat} {R : Roles X I O C} {c₀ : Config Nat} {q₀ : L.S} {addrs : List Nat}
    {p : IOAccept.Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) (i : I) (hi : Tag.inp i ∈ ts) :
    ∃ o, (∃ c, calloutAt? m memAddr c = some o) ∧
      (R.callIn o = some i ∨ ∃ wr, R.answerIn o wr = some i) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.tsession_inputs h i hi

/-- **Without a `sexp` import a module accepts only atoms.** -/
theorem memWriterLang_subset_atoms {P : Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : MemImports} {pol : Policy (BitVec 32)}
    (hs : ∀ i ∈ m.imports, (i.moduleName, i.name) ≠ ix.sexp) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P Envs memIdx m ix pol ⊆ {x | ∃ a, x = .atom a} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.memWriterLang_subset_atoms hs ha hw

end Silmaril.Wasm.Game.HandleAccept.Memory
