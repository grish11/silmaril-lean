module

public import Silmaril.Wasi.Component.Accept.Inst.Defs
public import Silmaril.Wasi.Component.Accept.Consequence.Thms
public import Silmaril.Wasm.Component.InstExport.Thms
public import Silmaril.Wasm.Component.Binary.Lower.SemI.Thms

/-! # Component acceptors with an instantiation phase: theorems

* `compModelI_toI`, `ofIRI_toI`, `langI_toI`: for a start-free core semantics `C` (seen through
  `CoreSem.toI`), the instantiation-aware reading **is** the start-free one
  (`Comp.denX C.toI = Comp.denU C`, `Silmaril.Wasm.Component.denX_toI`).
* `langI_core3_le`: for the Core 3.0 pipeline, on a lowered component all of whose core modules
  have an engine instance and no start function (`Comp.AllCore (Binary.StartFree P)`), the
  instantiation-aware language is included in the start-free one:
  `langI (coreModSemI P) L c ≤ (ofIR (coreModSem P) L c).lang`. The reverse inclusion (hence
  equality) is **not proved**: it needs that the IR's wiring exercises its nodes only along the
  instantiation protocol (`Silmaril.Wasm.Component.InstExport.Thms`).
* `componentBytesSystemI_iff`, `componentBytesSystemI_of_decode`,
  `componentBytesSystemI_of_decode_none`: what component bytes prove, as for
  `componentBytesSystem`; `componentBytesSystemCore3I_le`: on bytes lowering to such a
  start-free component, a judgement of `componentBytesSystemCore3I P` is one of
  `componentBytesSystemCore3 P`.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Consequence (System)
open Silmaril.Wasm.Component (Comp CoreModule CoreSem CoreSemI)

namespace ComponentAcceptor

variable {M : Type} [CoreModule M] (L : Layout) (acc : FnName) (rej : Option FnName)
  (mode : Mode)

theorem compModelI_toI (C : CoreSem M) (c : Comp M) : L.compModelI C.toI c = L.compModel C c := by
  rw [Layout.compModelI, Silmaril.Wasm.Component.denX_toI]; rfl

/-- **For a start-free core semantics the instantiation-aware acceptor is the start-free one.** -/
theorem ofIRI_toI (C : CoreSem M) (c : Comp M) :
    ofIRI C.toI L c acc rej mode = ofIR C L c acc rej mode := by
  rw [ofIRI, compModelI_toI]; rfl

theorem langI_toI (C : CoreSem M) (c : Comp M) :
    langI C.toI L c acc rej mode = (ofIR C L c acc rej mode).lang := by
  rw [langI, ofIRI_toI]

/-- **On start-free lowered components, ready-then-export acceptance is included in the
start-free acceptance** of the Core 3.0 pipeline. -/
theorem langI_core3_le {P : Silmaril.Wasm.Numerics.Profile}
    {c : Comp Silmaril.Wasm.Component.Binary.CoreMod}
    (hc : c.AllCore (Silmaril.Wasm.Component.Binary.StartFree P)) :
    langI (Silmaril.Wasm.Component.Binary.coreModSemI P) L c acc rej mode ≤
      (ofIR (Silmaril.Wasm.Component.Binary.coreModSem P) L c acc rej mode).lang := by
  have hv := Layout.view_mono L (Silmaril.Wasm.Component.Binary.denX_coreModSemI_le hc)
  cases mode
  · exact importAccepted_mono hv
  · exact exportAccepted_mono hv

end ComponentAcceptor

section Simple

variable (C : CoreSemI Silmaril.Wasm.Component.Binary.CoreMod) (mode : Mode) {b : ByteArray}
  {w : List UInt8}

/-- **What component bytes prove, with an instantiation phase**: exactly the bytes their lowered
component accepts after a successful instantiation. -/
theorem componentBytesSystemI_iff :
    componentBytesSystemI C mode b w ↔ ∃ c, ComponentAcceptor.decodeBinary b = some c ∧
      w ∈ (ComponentAcceptor.ofCompI C c mode).lang := Iff.rfl

theorem componentBytesSystemI_of_decode {c : Comp Silmaril.Wasm.Component.Binary.CoreMod}
    (h : ComponentAcceptor.decodeBinary b = some c) :
    componentBytesSystemI C mode b w ↔ w ∈ (ComponentAcceptor.ofCompI C c mode).lang :=
  System.ofDecoder_of_eq_some _ h w

/-- Bytes that do not parse and lower as a component prove nothing. -/
theorem componentBytesSystemI_of_decode_none (h : ComponentAcceptor.decodeBinary b = none) :
    ¬ componentBytesSystemI C mode b w :=
  System.ofDecoder_of_eq_none _ h w

/-- **On bytes lowering to a start-free component, the instantiation-aware Core 3.0 system
proves only what `componentBytesSystemCore3` proves.** -/
theorem componentBytesSystemCore3I_le {P : Silmaril.Wasm.Numerics.Profile}
    {c : Comp Silmaril.Wasm.Component.Binary.CoreMod}
    (h : ComponentAcceptor.decodeBinary b = some c)
    (hc : c.AllCore (Silmaril.Wasm.Component.Binary.StartFree P))
    (hw : componentBytesSystemCore3I P mode b w) : componentBytesSystemCore3 P mode b w := by
  rw [componentBytesSystemCore3I, componentBytesSystemI_of_decode _ _ h] at hw
  rw [componentBytesSystemCore3, componentBytesSystem_of_decode _ _ h]
  exact ComponentAcceptor.langI_core3_le _ _ _ _ hc hw

end Simple

end Silmaril.Wasi.Accept
