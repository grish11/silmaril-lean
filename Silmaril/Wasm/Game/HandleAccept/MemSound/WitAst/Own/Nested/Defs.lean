module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Checked.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested

open Silmaril.Formats Silmaril.Wasm.Game.Accept Silmaril.Wasm.Execution.Core

mutual
/-- Replace owned resource leaves by their ABI table index, retaining the rest of the shape. -/
def rawType : PTy → PTy
  | .own _ => .u32
  | .list element => .list (rawType element)
  | .fixedList element length => .fixedList (rawType element) length
  | .record fields => .record (rawFields fields)
  | .tuple types => .tuple (rawTypes types)
  | .variant cases => .variant (rawCases cases)
  | .option element => .option (rawType element)
  | .result ok error => .result (rawOpt ok) (rawOpt error)
  | type => type

def rawTypes : List PTy → List PTy
  | [] => []
  | type :: types => rawType type :: rawTypes types

def rawFields : List (String × PTy) → List (String × PTy)
  | [] => []
  | (name, type) :: fields => (name, rawType type) :: rawFields fields

def rawCases : List (String × Option PTy) → List (String × Option PTy)
  | [] => []
  | (name, type) :: cases => (name, rawOpt type) :: rawCases cases

def rawOpt : Option PTy → Option PTy
  | none => none
  | some type => some (rawType type)
end

abbrev rawSignature (S : WitSig) : WitSig := ⟨S.Tag, fun tag => rawTypes (S.params tag), S.arity⟩

/-- Indices reserved for this import, newest first. Distinct indices may carry identical
representations; duplicate detection is on the table index, not the representation. -/
abbrev Reservations := { handles : List (BitVec 32) // handles.Nodup }

abbrev Resolve := StateT Reservations (Except ResourceIssue)

/-- Locate a live, correctly typed resource and reserve its move. Nothing is killed yet. -/
def reserve (rt : RT) (resource : Nat) (index : BitVec 32) : Resolve Nat := do
  let reserved ← get
  if fresh : index ∉ reserved.val then
    match lookupChecked rt resource index with
    | .error failure => throw failure
    | .ok representation =>
      set (⟨index :: reserved.val, List.nodup_cons.mpr ⟨fresh, reserved.property⟩⟩ : Reservations)
      return representation
  else throw .duplicate

/-- Resolve a fixed list in the same order as a variable list, while retaining its length. -/
def resolveSized {M : Type → Type} [Monad M] {Raw Value : Type} (resolveOne : Raw → M Value) :
    (input : List Raw) → M { output : List Value // output.length = input.length }
  | [] => pure ⟨[], rfl⟩
  | head :: tail => do
    let value ← resolveOne head
    let values ← resolveSized resolveOne tail
    return ⟨value :: values.val, congrArg Nat.succ values.property⟩

section

variable {M : Type → Type} [Monad M] (move : Nat → BitVec 32 → M Nat)

mutual
/-- Resolve the active values in memory order. Descend through every compound constructor,
but never move a handle from an absent field or an inactive branch. -/
def resolveWith : (type : PTy) → (rawType type).Val → M type.Val
  | .own resource, index => move resource index.toBitVec
  | .list element, values => values.mapM (resolveWith element)
  | .fixedList element length, values => do
    let resolved ← resolveSized (resolveWith element) values.toList
    return ⟨resolved.val.toArray, by
      simpa only [List.size_toArray] using resolved.property.trans (by
        simpa only [Vector.toList, Array.length_toList] using values.2)⟩
  | .record fields, values => resolveFieldsWith fields values
  | .tuple types, values => resolveTypesWith types values
  | .variant cases, value => resolveCasesWith cases value
  | .option _, none => pure none
  | .option element, some value => some <$> resolveWith element value
  | .result ok _, .inl value => Sum.inl <$> resolveOptWith ok value
  | .result _ error, .inr value => Sum.inr <$> resolveOptWith error value
  | .bool, value | .s32, value | .u32, value | .s64, value | .u64, value | .string, value
  | .s8, value | .u8, value | .s16, value | .u16, value | .f32, value | .f64, value
  | .char, value | .enum _, value | .flags _, value => pure value
  | .borrow _, value => nomatch value

def resolveTypesWith : (types : List PTy) → PTy.Vals (rawTypes types) → M (PTy.Vals types)
  | [], _ => pure ()
  | type :: types, (value, values) => do
    let head ← resolveWith type value
    let tail ← resolveTypesWith types values
    pure (head, tail)

def resolveFieldsWith : (fields : List (String × PTy)) →
    PTy.FieldVals (rawFields fields) → M (PTy.FieldVals fields)
  | [], _ => pure ()
  | (_, type) :: fields, (value, values) => do
    let head ← resolveWith type value
    let tail ← resolveFieldsWith fields values
    pure (head, tail)

def resolveCasesWith : (cases : List (String × Option PTy)) →
    PTy.CaseVals (rawCases cases) → M (PTy.CaseVals cases)
  | [], value => nomatch value
  | (_, type) :: _, .inl value => Sum.inl <$> resolveOptWith type value
  | _ :: cases, .inr value => Sum.inr <$> resolveCasesWith cases value

def resolveOptWith : (type : Option PTy) → PTy.OptVal (rawOpt type) → M (PTy.OptVal type)
  | none, _ => pure ()
  | some type, value => resolveWith type value
end

end

abbrev resolve (rt : RT) := resolveWith (reserve rt)
abbrev resolveTypes (rt : RT) := resolveTypesWith (reserve rt)
abbrev resolveFields (rt : RT) := resolveFieldsWith (reserve rt)
abbrev resolveCases (rt : RT) := resolveCasesWith (reserve rt)
abbrev resolveOpt (rt : RT) := resolveOptWith (reserve rt)

variable (S : WitSig) (tagOf : BitVec 32 → Option S.Tag)

/-- Successful traversal carries a distinct set of indices in addition to the typed value.
The caller commits it only after the whole import has passed validation. -/
def reserveOp (rt : RT) (raw : Op (rawSignature S)) : Except NodeIssue (Op S × Reservations) := do
  (checkPTys .recursiveOwn (S.params raw.1)).mapError .payload
  let (values, reserved) ← ((resolveTypes rt (S.params raw.1) raw.2).run ⟨[], .nil⟩).mapError .resource
  return (⟨raw.1, values⟩, reserved)

/-- Checked memory-backed node construction with recursive owned resource lifting.
All reservations are local to this import and committed together on a successful result. -/
def checkedNode (mode : NodeMode) (rt : RT) (observed : Callout) :
    Except NodeIssue ((Op S × List (BitVec 32)) × RT) := do
  let args ← preflightNode S tagOf .recursiveOwn mode observed
  let (raw, children) ← decodeNodePayload (rawSignature S) mode args observed
  let (value, reserved) ← reserveOp S rt raw
  return ((value, children), rt.killAll reserved.val)

/-- An unsupported schema or a malformed nested resource traps only the current call. -/
def checkedNodeReply (mode : NodeMode) (rt : RT) (imp : String × String) (memory : Nat)
    (call : UCall Nat) (onSuccess : (Op S × List (BitVec 32)) × RT → UReply → Prop) : UReply → Prop :=
  checkedReply (checkedAt mode imp memory call (checkedNode S tagOf mode rt)) call onSuccess

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested
