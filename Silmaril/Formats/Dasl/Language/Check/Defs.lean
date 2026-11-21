module

public import Mathlib.Data.Finset.Sort
public import Silmaril.Formats.Dasl.Language.Defs
public import Silmaril.Semantics.Naming.Query.Defs

public section

namespace Silmaril.Formats.Dasl.Check

open Silmaril.Semantics.Naming

variable {Name : Type} {store : Store Name}

inductive Fault (Name : Type) where
  | fuel (link : Link Name)
  | missing (link : Link Name)
  | invalid (link : Link Name)
  deriving DecidableEq

inductive Outcome (Name : Type) where
  | accepted
  | rejected
  | undecided (fault : Fault Name)
  deriving DecidableEq

private def atLink (link : Link Name) : ReadFailure → Fault Name
  | .missing => .missing link
  | .invalid => .invalid link

private def sequenceFin {Error : Type} : (len : Nat) → {Result : Fin len → Type} →
    ((index : Fin len) → Except Error (Result index)) → Except Error ((index : Fin len) → Result index)
  | 0, _, _ => .ok (fun index => nomatch index)
  | len + 1, _, fetch => do
    let first ← fetch 0
    let tail ← sequenceFin len (fun index => fetch index.succ)
    pure (Fin.cases first tail)

private def sequenceMembers {Error : Type} : (keys : List String) →
    {Result : (key : String) → key ∈ keys → Type} →
    ((key : String) → (member : key ∈ keys) → Except Error (Result key member)) →
    Except Error ((key : String) → (member : key ∈ keys) → Result key member)
  | [], _, _ => .ok (fun _ member => (List.not_mem_nil member).elim)
  | head :: tail, Result, fetch => do
    let first ← fetch head (List.mem_cons_self ..)
    let rest ← sequenceMembers tail (Result := fun key hit => Result key (List.mem_cons_of_mem _ hit))
      (fun key hit => fetch key (List.mem_cons_of_mem _ hit))
    pure (fun key member => if same : key = head then by subst key; exact first
      else rest key ((List.mem_cons.mp member).resolve_left same))

/-- Recurse through inline syntax while delegating CAS dereferences to a policy.
Successful child expansions carry the proofs needed for the parent. -/
def resolveInline
    (objects : (name : Name) → Except (Fault Name) {value // FullNames store name value})
    (blobs : (name : Name) → Except (Fault Name) {value // store.blobs name value}) :
    (source : Shallow Name) → Except (Fault Name) {value // Expands store source value}
  | .ref (.obj name) => do
    let ⟨target, hit⟩ ← objects name
    pure ⟨.obj name target, let ⟨_, present, expanded⟩ := hit; .obj present expanded⟩
  | .ref (.blob name) => do
    let ⟨bytes, hit⟩ ← blobs name
    pure ⟨.blob name bytes, .blob hit⟩
  | .obj impossible _ | .blob impossible _ => impossible.elim
  | .dict keys children => do
    let expanded ← sequenceMembers keys.sort (Result := fun key member =>
      {value // Expands store (children ⟨key, (Finset.mem_sort _).mp member⟩) value}) (fun key member =>
      resolveInline objects blobs (children ⟨key, (Finset.mem_sort _).mp member⟩))
    let targets := fun (key : ↥keys) => expanded key.val ((Finset.mem_sort _).mpr key.property)
    pure ⟨.dict keys (fun key => (targets key).val), .dict (fun key => (targets key).property)⟩
  | .list len children => do
    let expanded ← sequenceFin len (fun index => resolveInline objects blobs (children index))
    pure ⟨.list len (fun index => (expanded index).val), .list (fun index => (expanded index).property)⟩
  | .i64 bits => .ok ⟨.i64 bits, .i64 bits⟩
  | .bytes bytes => .ok ⟨.bytes bytes, .bytes bytes⟩
  | .string text => .ok ⟨.string text, .string text⟩
  | .bool value => .ok ⟨.bool value, .bool value⟩
  | .null => .ok ⟨.null, .null⟩
termination_by structural source => source

/-- Fuel counts links per path, not the root read or inline constructors.
Missing, invalid and exhausted reads abort; none is a negative language answer. -/
def resolve (queries : Queries store) : (fuel : Nat) → (root : Name) →
    Except (Fault Name) {value // FullNames store root value}
  | 0, root => do
    let ⟨source, hit⟩ ← (queries.readObject root).mapError (atLink (.obj root))
    let ⟨target, expanded⟩ ← resolveInline (fun name => .error (.fuel (.obj name)))
      (fun name => .error (.fuel (.blob name))) source
    pure ⟨target, source, hit, expanded⟩
  | fuel + 1, root => do
    let ⟨source, hit⟩ ← (queries.readObject root).mapError (atLink (.obj root))
    let ⟨target, expanded⟩ ← resolveInline (resolve queries fuel)
      (fun name => (queries.readBlob name).mapError (atLink (.blob name))) source
    pure ⟨target, source, hit, expanded⟩

@[expose] def classify {root : Name} (accepts : Value → Bool) :
    Except (Fault Name) {value // FullNames store root value} → Outcome Name
  | .ok ⟨target, _⟩ => if accepts target.erase then .accepted else .rejected
  | .error fault => .undecided fault

@[expose] def run (queries : Queries store) (accepts : Value → Bool) (fuel : Nat) (root : Name) : Outcome Name :=
  classify accepts (resolve queries fuel root)

end Silmaril.Formats.Dasl.Check
