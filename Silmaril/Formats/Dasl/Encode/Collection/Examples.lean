module

import Mathlib.Data.String.Basic
import Silmaril.Formats.Dasl.Encode.Collection.Thms
import Silmaril.Formats.Dasl.Encode.Collection.Optimized.Defs

namespace Silmaril.Formats.Dasl.Encode.CollectionExamples

open Silmaril.Semantics

private def fees : OrderedMap String Int64 :=
  OrderedMap.ofLookupOn {"standard", "student"} fun key =>
    if key = "standard" then some 12 else if key = "student" then some 5 else none

private def pairFees : TotalCodec (OrderedMap String Int64) (Shallow Unit) :=
  finiteMap pairEntry text signed

private def recordFees : TotalCodec (OrderedMap String Int64) (Shallow Unit) :=
  finiteMap recordEntry text signed

example : RepresentsMap pairFees (pairFees.encode fees) fees.lookup? :=
  ⟨fees, pairFees.recovers fees, rfl⟩

example : RepresentsMap recordFees (recordFees.encode fees) fees.lookup? :=
  ⟨fees, recordFees.recovers fees, rfl⟩

example : fees.lookup? "guest" = none := by simp [fees]

private def seasons : Finset Int64 := {-2, -1, 0, 1, 8}

private def rangeSeasons : TotalCodec (Finset Int64) (Shallow Unit) := signedRangeSet

example : RepresentsSet rangeSeasons (rangeSeasons.encode seasons) (seasons : Set Int64) :=
  ⟨seasons, rangeSeasons.recovers seasons, rfl⟩

end Silmaril.Formats.Dasl.Encode.CollectionExamples
