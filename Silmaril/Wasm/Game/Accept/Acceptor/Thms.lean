module

public import Silmaril.Wasm.Game.Accept.Acceptor.Defs
public import Silmaril.Wasm.Game.Accept.Bounds.Thms
public import Silmaril.Wasm.Game.Accept.Reject.Thms

/-! # Module acceptors: theorems

* The CSLib language of a module acceptor is `lang` (`acceptor_language`).
* **Length bounds by address width**: an accepted string is shorter than `addrBound A.addr`
  (`length_lt`), so `lang` and `strictLang` are finite (`lang_finite`, `strictLang_finite`).
* `lang` is the byte language of `Silmaril.Wasm.Game.Accept` for the default 32-bit acceptor
  (`lang_default`).
* Callout-equivalent modules give the same languages (`lang_eq_of_calloutEquiv`, …).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.Accept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Formats.Accept

namespace ModuleAcceptor

variable (A : ModuleAcceptor)

@[simp] theorem acceptor_language : Cslib.Automata.Acceptor.language A = A.lang := rfl

theorem lang_default (P : Profile) (m : Module) :
    lang { profile := P, module := m } = bytesLang P m := rfl

theorem length_lt {w : List UInt8} (h : w ∈ A.lang) : w.length < addrBound A.addr := by
  rcases A with ⟨P, m, acc, rej, k, a, E⟩
  cases a
  · exact accepted_bytes32_length_lt h
  · exact accepted_bytes64_length_lt h

theorem lang_finite : (A.lang : Set (List UInt8)).Finite :=
  ByteLang.finite_of_length_lt fun _ h => A.length_lt h

theorem strictLang_le : A.strictLang ≤ A.lang := inf_le_left

theorem strictLang_finite : (A.strictLang : Set (List UInt8)).Finite :=
  A.lang_finite.subset A.strictLang_le

/-- Without a reject import, the strict language is the language. -/
theorem strictLang_of_reject_none (h : A.reject = none) : A.strictLang = A.lang := by
  simp [strictLang, neverRejectedLang, h]

/-- The two acceptors differ only in the module, and those modules are callout-equivalent. -/
theorem lang_eq_of_calloutEquiv {B : ModuleAcceptor} (hP : A.profile = B.profile)
    (hE : A.envs = B.envs) (hk : A.memIdx = B.memIdx) (ha : A.accept = B.accept)
    (hw : A.addr = B.addr) (h : CalloutEquiv B.profile B.envs B.memIdx A.module B.module) :
    A.lang = B.lang := by
  unfold lang; rw [hP, hE, hk, ha, hw]; exact accepted_eq_of_calloutEquiv h _ _

theorem neverRejectedLang_eq_of_calloutEquiv {B : ModuleAcceptor} (hP : A.profile = B.profile)
    (hE : A.envs = B.envs) (hk : A.memIdx = B.memIdx) (hr : A.reject = B.reject)
    (hw : A.addr = B.addr) (h : CalloutEquiv B.profile B.envs B.memIdx A.module B.module) :
    A.neverRejectedLang = B.neverRejectedLang := by
  unfold neverRejectedLang; rw [hP, hE, hk, hr, hw]
  cases B.reject
  · rfl
  · exact neverRejected_eq_of_calloutEquiv h

end ModuleAcceptor

end Silmaril.Wasm.Game.Accept
