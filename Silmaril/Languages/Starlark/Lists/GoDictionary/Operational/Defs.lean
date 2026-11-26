module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Defs
public import Silmaril.Languages.Starlark.Lists.Comparison.Operational.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary

inductive Mixes (increment : UInt32) : List UInt32 → UInt32 → UInt32 → UInt32 → Prop where
  | empty (hash mult : UInt32) : Mixes increment [] hash mult hash
  | field {word hash mult out : UInt32} {rest : List UInt32} :
      Mixes increment rest (hash ^^^ (word * mult)) (mult + increment) out →
      Mixes increment (word :: rest) hash mult out

inductive FieldHashes (hashes : Value → UInt32 → Prop) : List Value → List UInt32 → Prop where
  | empty : FieldHashes hashes [] []
  | field {key : Value} {word : UInt32} {fields : List Value} {words : List UInt32} :
      hashes key word → FieldHashes hashes fields words → FieldHashes hashes (key :: fields) (word :: words)

inductive HashStep (heap : Heap) (next : Value → UInt32 → Prop) : Value → UInt32 → Prop where
  | none : HashStep heap next (.scalar .none) 0
  | boolean (flag : Bool) : HashStep heap next (.scalar (.bool flag)) (if flag then 1 else 0)
  | integer (value : Int) : HashStep heap next (.scalar (.int value)) (intHash value)
  | floating {bits : UInt64} {number : Binary64.Number} :
      Binary64.Decodes bits number → HashStep heap next (.scalar (.float bits)) (numberHash number)
  | tuple {address : Address} {fields : List Value} {words : List UInt32} {out : UInt32} :
      heap.tupleFields address = .ok fields →
      FieldHashes next fields words →
      Mixes (82520 + 2 * UInt32.ofNat words.length) words 0x345678 1000003 out →
      HashStep heap next (.tuple address) out

def HashesAt (heap : Heap) : Nat → Value → UInt32 → Prop
  | 0, _, _ => False
  | depth + 1, key, out => HashStep heap (HashesAt heap depth) key out

/-- Lookup hashes before probing and retains the first reached probe error. -/
inductive LooksUp (heap : Heap) (bucket : Bucket) (key : Value) :
    Except Error (UInt32 × Option (Row × Nat)) → Prop where
  | hashError {error : Error} : hashKey heap key = .error error →
      LooksUp heap bucket key (.error error)
  | probed {hash : UInt32} {out : Except Lists.Error (Option (Row × Nat))} :
      HashesAt heap (heap.size + 1) key hash →
      Comparison.Probes (fun candidate => Comparison.EqualAt heap Comparison.defaultDepth key candidate.1.key)
        (bucket.candidates (storedHash hash)) out →
      LooksUp heap bucket key ((out.mapError .runtime).map fun hit => (storedHash hash, hit))

end Silmaril.Languages.Starlark.Lists.GoDictionary
