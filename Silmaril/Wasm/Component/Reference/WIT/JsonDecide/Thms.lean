module

public import Silmaril.Wasm.Component.Reference.WIT.Json.Thms
public import Silmaril.Formats.JsonBytes.Decide.Thms
public import Silmaril.Wasi.Component.Accept.Stream.Monitor.Thms
import Silmaril.Proofs.Wasm.Component.Reference.WIT.JsonInfinite

/-! # The JSON decider (#266) in the acceptor vocabulary

* `textB p` is exact for the JSON byte language as an acceptor set
  (`exact_ofBool_textB`, via `Lang.exact_ofBool_iff`).
* **The JSON byte language is infinite** (`json_language_infinite`): `n` spaces followed by `0`
  is a JSON text for every `n`. This discharges the hypothesis of
  `ModuleAcceptor.not_complete_json_of_infinite`. So **no one-call `accept(ptr, len)` module is
  complete for JSON**, under either profile (`ModuleAcceptor.not_complete_json`). It is still
  complete for nothing beyond a finite part (`Wasm.Game.Accept.Complete`). This is about the
  one-call interface only.
* Membership is decidable (#266), so JSON is a valid specification of incremental components:
  a `StreamCorrect` component's answer after the chunks of a JSON stream prefix is whether the
  prefix is a JSON text (`json_answer_eq_prefixAt`).

Proofs of infinitude: `Silmaril.Proofs.Wasm.Component.Reference.WIT.JsonInfinite`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

open Silmaril.Formats.Accept

/-- The decider is exact for the language. -/
theorem exact_ofBool_textB (p : Silmaril.Formats.JsonBytes.Profile) :
    Lang.Exact (Silmaril.Accept.ofBool (Silmaril.Formats.JsonBytes.Decide.textB p))
      (Silmaril.Formats.JsonBytes.language p) :=
  Lang.exact_ofBool_iff.2 fun _ => Silmaril.Formats.JsonBytes.Decide.textB_iff

/-- **The JSON byte language is infinite.** -/
theorem json_language_infinite (p : Silmaril.Formats.JsonBytes.Profile) :
    (Silmaril.Formats.JsonBytes.language p : Set (List UInt8)).Infinite :=
  Silmaril.Proofs.Wasm.Component.Reference.WIT.language_infinite p

end Silmaril.Wasm.Component.WIT

namespace Silmaril.Wasm.Game.Accept.ModuleAcceptor

/-- **No one-call module acceptor is complete for JSON.** -/
theorem not_complete_json (A : ModuleAcceptor) (p : Silmaril.Formats.JsonBytes.Profile) :
    ¬ Silmaril.Formats.Accept.Lang.Complete A.lang (Silmaril.Formats.JsonBytes.language p) :=
  A.not_complete_json_of_infinite (Silmaril.Wasm.Component.WIT.json_language_infinite p)

end Silmaril.Wasm.Game.Accept.ModuleAcceptor

namespace Silmaril.Wasi.Accept

open Silmaril.Games

/-- **A correct incremental JSON component answers each prefix by JSON validity.** -/
theorem json_answer_eq_prefixAt {I X : Set FnName} {fns : StreamFns}
    {σ : Strategy (nsig I) (nsig X)} {p : Silmaril.Formats.JsonBytes.Profile}
    (h : StreamCorrect fns σ (Silmaril.Formats.JsonBytes.language p))
    (cs : Silmaril.Streams.Chunks UInt8) (n : Nat) {t : List WEv} (ht : t ∈ Traces σ)
    (he : fns.events t = (cs.take n).map .process ++ [.query]) {b : Bool}
    (hb : (fns.answers t)[0]? = some b) :
    b = decide (cs.prefixAt n ∈ Silmaril.Formats.JsonBytes.language p) :=
  h.answer_eq_prefixAt cs n ht he hb

end Silmaril.Wasi.Accept
