module

public import Silmaril.Wasm.Component.Reference.WIT.Repr.Json.Defs
public import Silmaril.Wasm.Component.Reference.WIT.Repr.Thms
public import Silmaril.Formats.JsonEvents.Thms
public import Silmaril.Formats.JsonLines.Thms
import Silmaril.Proofs.Wasm.Component.Reference.WIT.Repr.Json

/-! # JSON event streams and JSON Lines as WIT values: theorems

**Event streams.**

* `treeEquiv`: JSON trees (`JsonEvents.Tree K S`, ordered, duplicates kept) are in bijection with
  the WIT `list<json-event>` values whose events are well formed. This composes
  `JsonEvents.equivLanguage` with the representation.
* `mem_events_language_iff`: such a value is well formed iff `ofEvents?` decodes it.
* `mem_eventLangAt_iff`: a WIT value is in the represented `eventLangAt okK okS d` iff it is the
  representation of the events of a tree with valid keys and scalars and depth at most `d`
  (the generic `DepthBound` is the tree depth, `JsonEvents.toEvents_mem_depthBound_iff`).
* **Transport.** Soundness, completeness and exactness of a WIT acceptor for the represented
  `eventLang` are those of its Lean pullback, by the generic `Repr.sound_lang_iff`,
  `Repr.complete_lang_iff` and `Repr.exact_lang_iff`. Bounded completeness:
  `completeWithin_depth_iff`, completeness within the represented depth bound is completeness of
  the pullback for `eventLangAt`.

**JSON Lines.**

* `mem_items_linesLang_iff`: a `list<list<u8>>` value is in the represented `linesLang` iff each
  line is allowed.
* `frameLang_eq`: the byte language is the framings of the item lists.
* `linesEquiv`: with a required final newline (NDJSON, `Policy.ndjson`), framing is a bijection
  between the allowed item lists and the byte language (`terminated_injOn`: lines without `0A`
  are recovered). With an optional final newline and blank lines the item list is not determined
  by the bytes (`JsonLines` docs), and no bijection is claimed.

**Not claimed.** No lexer from bytes to events: nothing relates `eventLang` to
`JsonBytes.language`, and the item lines are byte strings, not events. The proofs are in
`Silmaril.Proofs.Wasm.Component.Reference.WIT.Repr.Json`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

open Silmaril.Formats Silmaril.Formats.Accept

universe u v

variable {Ref : Type u} {Resource : Type v} {E : Env Ref Resource} {K S : Type}
  {tk ts : ValType Ref Resource}

namespace Json

/-- **Trees are in bijection with the well-formed WIT event streams.** -/
def treeEquiv (rk : Repr E K tk) (rs : Repr E S ts) :
    JsonEvents.Tree K S ≃
      {v : (ValType.list (eventType tk ts)).Interp E //
        v ∈ (Repr.events rk rs).lang (JsonEvents.language K S : Set _)} :=
  JsonEvents.equivLanguage.trans ((Repr.events rk rs).subtypeEquiv fun _ =>
    (Repr.mem_lang (Repr.events rk rs)).symm)

/-- A WIT event stream is well formed iff it decodes. -/
theorem mem_events_language_iff (rk : Repr E K tk) (rs : Repr E S ts)
    {v : (ValType.list (eventType tk ts)).Interp E} :
    v ∈ (Repr.events rk rs).lang (JsonEvents.language K S : Set _) ↔
      (JsonEvents.ofEvents? ((Repr.events rk rs).symm v)).isSome :=
  (Repr.mem_lang' _).trans JsonEvents.mem_language_iff

/-- **Valid bounded-depth WIT event streams are the representations of valid trees.** -/
theorem mem_eventLangAt_iff (rk : Repr E K tk) (rs : Repr E S ts) {okK : K → Prop}
    {okS : S → Prop} {d : Nat} {v : (ValType.list (eventType tk ts)).Interp E} :
    v ∈ (Repr.events rk rs).lang (eventLangAt okK okS d : Set _) ↔
      ∃ t : JsonEvents.Tree K S, Repr.events rk rs t.toEvents = v ∧
        (∀ e ∈ t.toEvents, ValidEvent okK okS e) ∧ t.depth ≤ d :=
  Silmaril.Proofs.Wasm.Component.Reference.WIT.Repr.Json.mem_eventLangAt_iff rk rs

/-- **Bounded completeness**: complete for valid streams within the depth bound iff the pullback
is complete for `eventLangAt`. -/
theorem completeWithin_depth_iff (rk : Repr E K tk) (rs : Repr E S ts) {okK : K → Prop}
    {okS : S → Prop} {d : Nat} {A : ValLang E (.list (eventType tk ts))} :
    Lang.CompleteWithin
        ((Repr.events rk rs).lang (Silmaril.Streams.DepthBound JsonEvents.Event.kind d : Set _))
        A ((Repr.events rk rs).lang (eventLang okK okS : Set _)) ↔
      Lang.Complete ((Repr.events rk rs).pull A) (eventLangAt okK okS d : Set _) :=
  (Repr.events rk rs).completeWithin_lang_iff

/-- A `list<list<u8>>` value is in the represented items language iff each line is allowed. -/
theorem mem_items_linesLang_iff {pol : JsonLines.Policy} {L : Language UInt8}
    {v : (ValType.list (.bytes : ValType Ref Resource)).Interp E} :
    v ∈ (Repr.items (E := E)).lang (linesLang pol L) ↔ ∀ l ∈ v, l ∈ JsonLines.lineOf pol L := by
  have h := (Repr.items (E := E)).mem_lang (S := linesLang pol L) (x := v)
  rw [Repr.items_apply] at h
  exact h

/-- The byte language is the framings of the allowed item lists. -/
theorem frameLang_eq (pol : JsonLines.Policy) (L : Language UInt8) :
    JsonLines.frameLang pol L = {w | ∃ ls ∈ linesLang pol L, JsonLines.Framed pol.final ls w} :=
  rfl

/-- Lines without `0A`, each terminated by `0A`, determine the lines. -/
theorem terminated_injOn {ls ls' : List (List UInt8)} (h : ∀ l ∈ ls, JsonLines.lf ∉ l)
    (h' : ∀ l ∈ ls', JsonLines.lf ∉ l)
    (he : JsonLines.terminated ls = JsonLines.terminated ls') : ls = ls' :=
  Silmaril.Proofs.Wasm.Component.Reference.WIT.Repr.Json.terminated_injOn h h' he

/-- **With a required final newline, items and bytes are in bijection.** -/
noncomputable def linesEquiv {pol : JsonLines.Policy} (hf : pol.final = .required)
    (L : Language UInt8) : {ls // ls ∈ linesLang pol L} ≃ {w // w ∈ JsonLines.frameLang pol L} :=
  Equiv.ofBijective (fun ls => ⟨JsonLines.terminated ls.1, ls.1, ls.2, by rw [hf]; rfl⟩)
    ⟨fun a b hab => Subtype.ext (terminated_injOn
        (fun l hl => JsonLines.not_mem_lf_of_mem_lineOf (a.2 l hl))
        (fun l hl => JsonLines.not_mem_lf_of_mem_lineOf (b.2 l hl))
        (by simpa using congrArg Subtype.val hab)),
     fun ⟨w, ls, hls, hw⟩ => ⟨⟨ls, hls⟩, Subtype.ext (by
        rw [hf] at hw; exact hw.symm)⟩⟩

end Json

end Silmaril.Wasm.Component.WIT
