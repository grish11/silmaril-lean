module

public import Silmaril.Wasi.Component.Accept.Acceptor.Quot.Defs
public import Silmaril.Wasi.Component.Accept.Acceptor.Thms
public import Silmaril.Semantics.Accept.Order.Thms

/-! # Acceptors up to semantic equivalence: theorems

* `calloutSetoid` and `traceSetoid` respect `lang`, `neverRejectedLang` and `strictLang`
  (`Silmaril.Accept.RespectsLang` instances), so each language descends to the quotient.
* `ByteAcceptor.lang` is `Silmaril.Accept.langSum` (`byteAcceptor_lang_eq_langSum`).
* **Canonical-ABI pairs are one language class** across shapes (`CanonPair.langEq_mk_eq`).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.Accept.ModuleAcceptor

instance : Silmaril.Accept.RespectsLang calloutSetoid lang :=
  ⟨fun A _ ⟨h₁, h₂, h₃, h₄, _, h₆, h₇⟩ => A.lang_eq_of_calloutEquiv h₁ h₂ h₃ h₄ h₆
    (by rw [← h₁, ← h₂, ← h₃]; exact h₇)⟩

instance : Silmaril.Accept.RespectsLang calloutSetoid neverRejectedLang :=
  ⟨fun A _ ⟨h₁, h₂, h₃, _, h₅, h₆, h₇⟩ => A.neverRejectedLang_eq_of_calloutEquiv h₁ h₂ h₃ h₅ h₆
    (by rw [← h₁, ← h₂, ← h₃]; exact h₇)⟩

instance : Silmaril.Accept.RespectsLang calloutSetoid strictLang :=
  ⟨fun _ _ h => by
    unfold strictLang
    rw [Silmaril.Accept.RespectsLang.eq_of_rel (lang := lang) h,
      Silmaril.Accept.RespectsLang.eq_of_rel (lang := neverRejectedLang) h]⟩

end Silmaril.Wasm.Game.Accept.ModuleAcceptor

namespace Silmaril.Wasi.Accept

open Silmaril.Wasm.Game.Accept (ModuleAcceptor)

namespace ComponentAcceptor

theorem lang_eq_of_traceRel {A B : ComponentAcceptor} (h : TraceRel A B) : A.lang = B.lang := by
  obtain ⟨h₁, -, h₃, h₄⟩ := h
  unfold lang; rw [← h₁, ← h₃]
  cases A.mode
  · exact importAccepted_eq_of_traces h₄
  · exact exportAccepted_eq_of_traces h₄

theorem neverRejectedLang_eq_of_traceRel {A B : ComponentAcceptor} (h : TraceRel A B) :
    A.neverRejectedLang = B.neverRejectedLang := by
  obtain ⟨-, h₂, h₃, h₄⟩ := h
  unfold neverRejectedLang; rw [← h₂, ← h₃]
  cases A.reject with
  | none => rfl
  | some r =>
    cases A.mode
    · exact neverCalled_eq_of_traces h₄
    · exact neverFalse_eq_of_traces h₄

instance : Silmaril.Accept.RespectsLang traceSetoid lang := ⟨fun _ _ h => lang_eq_of_traceRel h⟩

instance : Silmaril.Accept.RespectsLang traceSetoid neverRejectedLang :=
  ⟨fun _ _ h => neverRejectedLang_eq_of_traceRel h⟩

instance : Silmaril.Accept.RespectsLang traceSetoid strictLang :=
  ⟨fun _ _ h => by
    unfold strictLang; rw [lang_eq_of_traceRel h, neverRejectedLang_eq_of_traceRel h]⟩

end ComponentAcceptor

theorem byteAcceptor_lang_eq_langSum :
    ByteAcceptor.lang = Silmaril.Accept.langSum ModuleAcceptor.lang ComponentAcceptor.lang := rfl

/-- **A module and a component in canonical-ABI correspondence are one language class.** -/
theorem CanonPair.langEq_mk_eq {A : ModuleAcceptor} {B : ComponentAcceptor} (h : CanonPair A B) :
    Silmaril.Accept.LangEq.mk ByteAcceptor.lang (.inl A) =
      Silmaril.Accept.LangEq.mk ByteAcceptor.lang (.inr B) :=
  Silmaril.Accept.LangEq.mk_eq_mk_iff.2 h.lang_eq

end Silmaril.Wasi.Accept
