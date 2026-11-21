module

public import Silmaril.Wasm.Sublanguages.Thms
public import Silmaril.Wasm.Link.GC
public import Silmaril.Wasm.Binaryen.Exe.CoreInputCheck

/-! A certified read-back path from the existing partial Core GC linker. -/

@[expose] public section

namespace Silmaril.Wasm.Sublanguages

open Profiles Profiles.Injections
open Binaryen.Exe (canonicalModuleEq)

/-- A candidate reader must recover native syntax on its exact image. The
reader may succeed outside that image, for example on retagged syntax. -/
structure Readback (language : Language) where
  candidate : Wasm.Module → Option language.Module
  onImage : ∀ mod, candidate (language.toModule mod) = some mod

def coreReadback : Readback core := ⟨some, fun _ => rfl⟩

def wasm1Readback : Readback wasm1 := ⟨V1.Module.ofCore?, V1.Module.ofCore?_toCore⟩

def limeReadback : Readback lime := ⟨Lime1.Module.ofCore?, Lime1.Module.ofCore?_toCore⟩

def wasm2Readback : Readback wasm2 where
  candidate coreMod := do
    let mod ← V2.Module.ofCore? coreMod
    if valid : (wasm2ToWasm3.run mod).isSome then some ⟨mod, valid⟩ else none
  onImage source := by
    have exactImage := V2.Module.ofCore?_toCore (wasm2ToWasm3.onDomain_spec source)
    change (V2.Module.ofCore? (wasm2ToWasm3.onDomain source)).bind
      (fun mod => if valid : (wasm2ToWasm3.run mod).isSome then some (⟨mod, valid⟩ : wasm2.Module) else none) =
      some source
    rw [exactImage]; simp [source.property]; rfl

def functionalReadback (gc : GCMode) (exn : ExceptionMode) : Readback (functional gc exn) :=
  ⟨FunctionalCore.check? gc exn, fun source => by
    change FunctionalCore.check? gc exn source.val = some source
    rcases source with ⟨mod, admitted⟩; simp [FunctionalCore.check?, admitted]; rfl⟩

namespace Readback

variable {language : Language}

/-- Exact syntax checking after candidate read-back. The existing sound Core
comparison uses canonical encoding, so it may reject unencodable syntax. -/
def exact? (reader : Readback language) (coreMod : Wasm.Module) : Option language.Module := do
  let mod ← reader.candidate coreMod
  if canonicalModuleEq (language.toModule mod) coreMod then some mod else none

/-- Run the actual Core linker and read back only its exact result. This is
not an unconditional closure result for the source language. -/
def link? (reader : Readback language) (namespaceName : String) (provider consumer : language.Module) :
    Option language.Module := do
  let output ← Link.GC.link? namespaceName (language.toModule provider) (language.toModule consumer)
  reader.exact? output

end Readback

end Silmaril.Wasm.Sublanguages
