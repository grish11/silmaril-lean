module

public import Silmaril.Wasi.Component.Accept.Acceptor.Defs
public import Silmaril.Wasi.Component.Accept.Bounds.Thms
public import Silmaril.Wasi.Component.Accept.Reject.Thms
public import Silmaril.Wasm.Game.Accept.Acceptor.Thms

/-! # Component acceptors, and acceptors of either shape: theorems

* The CSLib languages are `lang` (`acceptor_language`, `ByteAcceptor.acceptor_language`).
  The sum's inclusions keep each shape's language (`ByteAcceptor.lang_inl`, `lang_inr`).
* **Canonical-ABI pairs accept the same bytes** (`CanonPair.lang_eq`). So the component
  inherits the module's address-width bound and finiteness (`CanonPair.length_lt`,
  `CanonPair.lang_finite`).
* `CompEquiv` IR components give equal languages (`ofIR_lang_of_compEquiv`, and the same for
  `neverRejectedLang` and `strictLang`). `CompRefines` gives an included language and a
  larger never-rejected language (`ofIR_lang_of_compRefines`,
  `ofIR_neverRejectedLang_of_compRefines`).
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Formats.Accept
open Silmaril.Wasm.Component (Comp CoreModule)
open Silmaril.Wasm.Component.Algebra (CompEquiv CompRefines)
open Silmaril.Wasm.Game.Accept (ModuleAcceptor)

namespace ComponentAcceptor

@[simp] theorem acceptor_language (A : ComponentAcceptor) :
    Cslib.Automata.Acceptor.language A = A.lang := rfl

theorem strictLang_le (A : ComponentAcceptor) : A.strictLang ≤ A.lang := inf_le_left

section IR

variable {M : Type} [CoreModule M] (C : Silmaril.Wasm.Component.CoreSem M) (L : Layout)
  {c c' : Comp M} (acc : FnName) (rej : Option FnName) (mode : Mode)

theorem ofIR_lang_of_compEquiv (h : CompEquiv C c c') :
    (ofIR C L c acc rej mode).lang = (ofIR C L c' acc rej mode).lang := by
  simp only [ofIR, Layout.compModel, h.2]

theorem ofIR_neverRejectedLang_of_compEquiv (h : CompEquiv C c c') :
    (ofIR C L c acc rej mode).neverRejectedLang = (ofIR C L c' acc rej mode).neverRejectedLang := by
  simp only [ofIR, Layout.compModel, h.2]

theorem ofIR_strictLang_of_compEquiv (h : CompEquiv C c c') :
    (ofIR C L c acc rej mode).strictLang = (ofIR C L c' acc rej mode).strictLang := by
  simp only [ofIR, Layout.compModel, h.2]

theorem ofIR_lang_of_compRefines (h : CompRefines C c c') :
    (ofIR C L c acc rej mode).lang ≤ (ofIR C L c' acc rej mode).lang := by
  have hv := Layout.view_mono L h.2
  cases mode
  · exact importAccepted_mono hv
  · exact exportAccepted_mono hv

theorem ofIR_neverRejectedLang_of_compRefines (h : CompRefines C c c') :
    (ofIR C L c' acc rej mode).neverRejectedLang ≤ (ofIR C L c acc rej mode).neverRejectedLang := by
  have hv := Layout.view_mono L h.2
  cases rej with
  | none => exact le_rfl
  | some r =>
    cases mode
    · exact neverCalled_anti hv
    · exact neverFalse_anti hv

end IR

end ComponentAcceptor

namespace ByteAcceptor

@[simp] theorem acceptor_language (A : ByteAcceptor) :
    Cslib.Automata.Acceptor.language A = A.lang := rfl

@[simp] theorem lang_inl (A : ModuleAcceptor) : lang (.inl A) = A.lang := rfl

@[simp] theorem lang_inr (B : ComponentAcceptor) : lang (.inr B) = B.lang := rfl

end ByteAcceptor

namespace CanonPair

variable {A : ModuleAcceptor} {B : ComponentAcceptor}

/-- **A module and a component in canonical-ABI correspondence accept the same bytes.** -/
theorem lang_eq (h : CanonPair A B) : A.lang = B.lang := by
  obtain ⟨hm, hc⟩ := h
  simp only [ComponentAcceptor.lang, hm]
  exact accepted_eq_of_canonLowerAcceptBy hc

/-- The same, for the sum of shapes. -/
theorem byteAcceptor_lang_eq (h : CanonPair A B) :
    ByteAcceptor.lang (.inl A) = ByteAcceptor.lang (.inr B) := h.lang_eq

/-- The component inherits the module's address-width bound. -/
theorem length_lt (h : CanonPair A B) {w : List UInt8} (hw : w ∈ B.lang) :
    w.length < Silmaril.Wasm.Game.Accept.addrBound A.addr :=
  A.length_lt (h.lang_eq ▸ hw)

theorem lang_finite (h : CanonPair A B) : (B.lang : Set (List UInt8)).Finite :=
  h.lang_eq ▸ A.lang_finite

end CanonPair

end Silmaril.Wasi.Accept
