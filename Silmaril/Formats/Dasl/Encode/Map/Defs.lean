module

public import Silmaril.Formats.Dasl.Encode.Defs
public import Silmaril.Semantics.OrderedMap.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Encode

open Silmaril.Semantics

variable {Name Ref Item Key : Type}

def pairEntry : TotalCodec (Tree Ref Name × Tree Ref Name) (Tree Ref Name) where
  encode entry := .list 2 (fun index => if index.val = 0 then entry.1 else entry.2)
  decode?
    | .list 2 values => some (values 0, values 1)
    | _ => none
  recovers _ := rfl

def recordKeys : Finset String := {"k", "v"}

def recordEncode (entry : Tree Ref Name × Tree Ref Name) : Tree Ref Name :=
  .dict recordKeys (fun key => if key.val = "k" then entry.1 else entry.2)

/-- Require exactly the two record fields; additional fields are not ignored. -/
def recordDecode : Tree Ref Name → Option (Tree Ref Name × Tree Ref Name)
  | .dict keys fields =>
    if same : keys = recordKeys then
      let values : ↥recordKeys → Tree Ref Name := same ▸ fields
      some (values ⟨"k", by decide⟩, values ⟨"v", by decide⟩)
    else none
  | _ => none

def recordEntry : TotalCodec (Tree Ref Name × Tree Ref Name) (Tree Ref Name) :=
  ⟨recordEncode, recordDecode, fun _ => rfl⟩

def OrderedMap.entriesCodec [LinearOrder Key] : TotalCodec (Semantics.OrderedMap Key Item) (List (Key × Item)) :=
  ⟨Semantics.OrderedMap.entries, Semantics.OrderedMap.ofEntries?,
    fun ⟨_, ordered⟩ => by simp [Semantics.OrderedMap.ofEntries?, ordered]⟩

end Silmaril.Formats.Dasl.Encode
