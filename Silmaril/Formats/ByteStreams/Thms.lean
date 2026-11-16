module

public import Silmaril.Formats.ByteStreams.Defs
public import Silmaril.Semantics.Acceptors.Thms

/-!
# Byte chunk streams: theorems

* `toList_eq_toBytes_*`: every byte chunk view is `BytesLike.toBytes`.
* `answer_iff_of_correctFold`: a `CorrectFold` acceptor for `L` answers yes after the chunks
  `cs` iff their concatenated bytes are in `L`.
* `answer_single_iff`: fed one value `b` as a single chunk, it answers yes iff `b ∈ᴮ L`.
* `exact_over`: as a Bool checker on single values, it is `Exact` for `L.over β`, in the
  sense of `Silmaril.Formats.Accept.Lang.Exact`.
-/

public section

namespace Silmaril.Formats.ByteStreams

open Silmaril.Formats.Accept Silmaril.Acceptor

universe u v

theorem toList_eq_toBytes_list (b : List UInt8) : ChunkView.toList b = toBytes b := rfl
theorem toList_eq_toBytes_array (b : Array UInt8) : ChunkView.toList b = toBytes b := rfl
theorem toList_eq_toBytes_byteArray (b : ByteArray) : ChunkView.toList b = toBytes b := rfl
theorem toList_eq_toBytes_kbytes (b : KBytes) : ChunkView.toList b = toBytes b := rfl
theorem toList_eq_toBytes_bytes (b : Formats.Bytes) : ChunkView.toList b = toBytes b := rfl

variable {σ : Type u} {β : Type v} [ChunkView β UInt8] [BytesLike β]
  {L : ByteLang} [DecidablePred (· ∈ L)]

/-- A correct acceptor answers membership of the concatenated bytes of its input chunks. -/
theorem answer_iff_of_correctFold (hv : ∀ b : β, ChunkView.toList b = toBytes b)
    {A : Acceptor σ β} (h : A.CorrectFold L) (cs : List β) :
    (A.query (cs.foldl A.process A.init)).1 = true ↔ cs.flatMap toBytes ∈ L := by
  rw [h, member_eq_true, List.flatMap_congr (fun b _ => hv b)]

/-- Fed one value as a single chunk, a correct acceptor answers `b ∈ᴮ L`. -/
theorem answer_single_iff (hv : ∀ b : β, ChunkView.toList b = toBytes b)
    {A : Acceptor σ β} (h : A.CorrectFold L) (b : β) :
    (A.query (A.process A.init b)).1 = true ↔ ByteLang.Accepts L b := by
  have := answer_iff_of_correctFold hv h [b]
  simpa [ByteLang.Accepts] using this

/-- As a checker on single values, a correct acceptor is exact for `L.over β`. -/
theorem exact_over (hv : ∀ b : β, ChunkView.toList b = toBytes b)
    {A : Acceptor σ β} (h : A.CorrectFold L) :
    Lang.Exact {b : β | (A.query (A.process A.init b)).1 = true} (L.over β) :=
  Set.ext fun b => answer_single_iff hv h b

end Silmaril.Formats.ByteStreams
