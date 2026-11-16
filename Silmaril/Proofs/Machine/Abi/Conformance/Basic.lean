module

public import Silmaril.Machine.Abi.Conformance.Defs
public import Silmaril.X86.FnContract.Thms

/-! # ABI conformance: the bridge from first-return function contracts -/

@[expose] public section

namespace Silmaril.Proofs.Machine.Abi.Conformance

open Silmaril.Machine.Abi.Conformance
open Silmaril.Machine.SystemV.Abi
open Silmaril.X86 (MState)
open Silmaril.X86.FnContract (Spec AbiEntry FirstReturn)

variable {A : AbiDef} {M : Mach} {mode : Mode} {hdr : HeaderSrc} {f : String} {p : A.V.Proto}
  {c : Code} {frame : Nat} {S : CallSpec A.V p}

theorem mem_callModelOf {s : Ffi.State} {t : MState} (h : FirstReturn M s.machine t) :
    { s with machine := t } ∈ callModelOf M s :=
  ⟨h, rfl⟩

/-- **A strict function contract gives a conformance row.** `S'` is a first-return contract
of the code on `M` (`Spec.Strict`); every admitted call meets its entry, and each of its
results is a conforming return. -/
theorem conforms_of_strict {S' : Spec MState} (hs : S'.Strict M)
    (hdecl : Declares A hdr f p) (hext : c.off + c.len ≤ c.bytes.length)
    (hnv : ∃ a s, Admit A M p c frame a s ∧ S.pre a s)
    (habi : ∀ a s, Admit A M p c frame a s → AbiEntry (M.core s.machine) (M.mem s.machine))
    (hentry : ∀ a s, Admit A M p c frame a s → S.pre a s → S'.entry s.machine)
    (hgood : ∀ a s t, Admit A M p c frame a s → S.pre a s → S'.Result M s.machine t →
      Good A p frame S a s { s with machine := t }) :
    Conforms A M mode hdr f p c frame S := by
  refine ⟨hdecl, hext, hnv, fun _ a s ad pre => ?_, fun a s ad pre t ht => ?_⟩
  · obtain ⟨t, fr, -⟩ := hs.firstReturn ad.live (habi a s ad) (hentry a s ad pre)
    exact ⟨_, mem_callModelOf fr⟩
  · obtain ⟨t0, fr, res⟩ := hs.firstReturn ad.live (habi a s ad) (hentry a s ad pre)
    obtain ⟨fr', heq⟩ := ht
    have := Silmaril.X86.FnContract.firstReturn_unique fr' fr
    rw [heq, this]
    exact hgood a s t0 ad pre res

/-- Conformance is not vacuous: an admitted call has a conforming return (total mode). -/
theorem Conforms.exists_good (h : Conforms A M .total hdr f p c frame S) :
    ∃ a s t, Admit A M p c frame a s ∧ t ∈ callModelOf M s ∧ Good A p frame S a s t := by
  obtain ⟨a, s, ad, pre⟩ := h.nonvacuous
  obtain ⟨t, ht⟩ := h.progress rfl a s ad pre
  exact ⟨a, s, t, ad, ht, h.sound a s ad pre t ht⟩

/-- A weaker spec (smaller precondition is not allowed: same admitted calls; weaker post, more
writes) is also met. -/
theorem Conforms.weaken {S₂ : CallSpec A.V p} (h : Conforms A M mode hdr f p c frame S)
    (hpre : ∀ a s, S₂.pre a s ↔ S.pre a s)
    (hpost : ∀ a s r t, S.pre a s → S.post a s r t → S₂.post a s r t)
    (hw : ∀ a s x, S.writes a s x → S₂.writes a s x) :
    Conforms A M mode hdr f p c frame S₂ := by
  refine ⟨h.declared, h.extent, ?_, fun hm a s ad pre => h.progress hm a s ad ((hpre a s).1 pre),
    fun a s ad pre t ht => ?_⟩
  · obtain ⟨a, s, ad, pre⟩ := h.nonvacuous
    exact ⟨a, s, ad, (hpre a s).2 pre⟩
  · have g := h.sound a s ad ((hpre a s).1 pre) t ht
    obtain ⟨r, hr, hp⟩ := g.result
    refine ⟨g.ret, ⟨r, hr, hpost a s r t ((hpre a s).1 pre) hp⟩, ?_⟩
    refine ⟨g.frame.1, fun x hx => g.frame.2 x fun hx' => hx ?_⟩
    rcases hx' with hx' | hx'
    · exact .inl (hw a s x hx')
    · exact .inr hx'

/-- A total row is a partial-correctness row. -/
theorem Conforms.toPartial (h : Conforms A M .total hdr f p c frame S) :
    Conforms A M .ifReturns hdr f p c frame S :=
  ⟨h.declared, h.extent, h.nonvacuous, (fun hm => nomatch hm), h.sound⟩

end Silmaril.Proofs.Machine.Abi.Conformance

end
