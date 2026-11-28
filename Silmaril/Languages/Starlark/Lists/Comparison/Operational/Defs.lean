module

public import Silmaril.Languages.Starlark.Lists.Comparison.Defs
public import Silmaril.Languages.Starlark.Comparison.Operational.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.Comparison

/-- An ordered scan records the decisive item or first reached error. -/
inductive Scans {α : Type} (tests : α → Except Error Bool → Prop) (decisive : Bool) :
    List α → Except Error Bool → Prop where
  | empty : Scans tests decisive [] (.ok (!decisive))
  | stopped {item : α} {rest : List α} :
      tests item (.ok decisive) → Scans tests decisive (item :: rest) (.ok decisive)
  | failed {item : α} {rest : List α} {error : Error} :
      tests item (.error error) → Scans tests decisive (item :: rest) (.error error)
  | continued {item : α} {rest : List α} {out : Except Error Bool} :
      tests item (.ok (!decisive)) → Scans tests decisive rest out →
      Scans tests decisive (item :: rest) out

/-- Key lookup selects the first entry with the requested canonical code. -/
inductive LooksUp (key : Key) : List Entry → Option Entry → Prop where
  | missing : LooksUp key [] none
  | hit {entry : Entry} {rest : List Entry} : entry.keyCode = key →
      LooksUp key (entry :: rest) (some entry)
  | skip {entry : Entry} {rest : List Entry} {out : Option Entry} : entry.keyCode ≠ key →
      LooksUp key rest out → LooksUp key (entry :: rest) out

/-- The checked dictionary lookup reads the receiver, validates the key, and
searches its entries in that order. -/
inductive DictionaryLookup (heap : Heap) (address : Address) (key : Value) :
    Except Error (Option Entry) → Prop where
  | receiverError {error : Error} : dictionaryEntries heap address = .error error →
      DictionaryLookup heap address key (.error error)
  | keyError {entries : List Entry} {error : Error} : dictionaryEntries heap address = .ok entries →
      ({ heap := heap } : State).keyOf key = .error error → DictionaryLookup heap address key (.error error)
  | searched {entries : List Entry} {code : Key} {out : Option Entry} :
      dictionaryEntries heap address = .ok entries → ({ heap := heap } : State).keyOf key = .ok code →
      LooksUp code entries out → DictionaryLookup heap address key (.ok out)

/-- A candidate probe records the winning candidate or the first reached error. -/
inductive Probes {α : Type} (tests : α → Except Error Bool → Prop) :
    List α → Except Error (Option α) → Prop where
  | missing : Probes tests [] (.ok none)
  | hit {candidate : α} {later : List α} : tests candidate (.ok true) →
      Probes tests (candidate :: later) (.ok (some candidate))
  | failed {candidate : α} {later : List α} {error : Error} : tests candidate (.error error) →
      Probes tests (candidate :: later) (.error error)
  | skip {candidate : α} {later : List α} {out : Except Error (Option α)} :
      tests candidate (.ok false) → Probes tests later out → Probes tests (candidate :: later) out

/-- Lookup is completed before comparing the selected values. -/
inductive ComparesEntry (next : Value → Value → Except Error Bool → Prop)
    (right : List Entry) (left : Entry) : Except Error Bool → Prop where
  | missing : LooksUp left.keyCode right none → ComparesEntry next right left (.ok false)
  | found {entry : Entry} {out : Except Error Bool} : LooksUp left.keyCode right (some entry) →
      next left.value entry.value out → ComparesEntry next right left out

/-- One nonzero level of comparison. The length check precedes the field or
entry scan. Addresses and insertion positions do not match dictionary keys. -/
inductive EqualStep (heap : Heap) (next : Value → Value → Except Error Bool → Prop)
    (left right : Value) : Except Error Bool → Prop where
  | scalar {a b : Starlark.Value} {flag : Bool} :
      Pair.ofValues left right = .scalars a b → Starlark.Compares .eq a b (.ok (.bool flag)) →
      EqualStep heap next left right (.ok flag)
  | string {a b : String} :
      Pair.ofValues left right = .strings a b →
      EqualStep heap next left right (.ok (decide (a = b)))
  | different : Pair.ofValues left right = .different → EqualStep heap next left right (.ok false)
  | unsupported : Pair.ofValues left right = .unsupported →
      EqualStep heap next left right (.error (.comparisonType left right))
  | leftError {kind : SequenceKind} {a b : Address} {error : Error} :
      Pair.ofValues left right = .sequences kind a b → kind.elements heap a = .error error →
      EqualStep heap next left right (.error error)
  | rightError {kind : SequenceKind} {a b : Address} {xs : List Value} {error : Error} :
      Pair.ofValues left right = .sequences kind a b →
      kind.elements heap a = .ok xs → kind.elements heap b = .error error →
      EqualStep heap next left right (.error error)
  | lengthMismatch {kind : SequenceKind} {a b : Address} {xs ys : List Value} :
      Pair.ofValues left right = .sequences kind a b →
      kind.elements heap a = .ok xs → kind.elements heap b = .ok ys → xs.length ≠ ys.length →
      EqualStep heap next left right (.ok false)
  | fields {kind : SequenceKind} {a b : Address} {xs ys : List Value} {out : Except Error Bool} :
      Pair.ofValues left right = .sequences kind a b →
      kind.elements heap a = .ok xs → kind.elements heap b = .ok ys → xs.length = ys.length →
      Scans (fun pair => next pair.1 pair.2) false (xs.zip ys) out →
      EqualStep heap next left right out
  | dictLeftError {a b : Address} {error : Error} :
      Pair.ofValues left right = .dictionaries a b → dictionaryEntries heap a = .error error →
      EqualStep heap next left right (.error error)
  | dictRightError {a b : Address} {xs : List Entry} {error : Error} :
      Pair.ofValues left right = .dictionaries a b →
      dictionaryEntries heap a = .ok xs → dictionaryEntries heap b = .error error →
      EqualStep heap next left right (.error error)
  | dictLengthMismatch {a b : Address} {xs ys : List Entry} :
      Pair.ofValues left right = .dictionaries a b →
      dictionaryEntries heap a = .ok xs → dictionaryEntries heap b = .ok ys → xs.length ≠ ys.length →
      EqualStep heap next left right (.ok false)
  | dictEntries {a b : Address} {xs ys : List Entry} {out : Except Error Bool} :
      Pair.ofValues left right = .dictionaries a b →
      dictionaryEntries heap a = .ok xs → dictionaryEntries heap b = .ok ys → xs.length = ys.length →
      Scans (ComparesEntry next ys) false xs out → EqualStep heap next left right out

def EqualAt (heap : Heap) : Nat → Value → Value → Except Error Bool → Prop
  | 0, _, _, out => out = .error .comparisonDepth
  | depth + 1, left, right, out => EqualStep heap (EqualAt heap depth) left right out

inductive ContainsAt (heap : Heap) (depth : Nat) (needle target : Value) : Except Error Bool → Prop where
  | unsupported : MembershipTarget.ofValue target = .unsupported →
      ContainsAt heap depth needle target (.error (.membershipTarget target))
  | readError {kind : SequenceKind} {address : Address} {error : Error} :
      MembershipTarget.ofValue target = .sequence kind address → kind.elements heap address = .error error →
      ContainsAt heap depth needle target (.error error)
  | fields {kind : SequenceKind} {address : Address} {xs : List Value} {out : Except Error Bool} :
      MembershipTarget.ofValue target = .sequence kind address → kind.elements heap address = .ok xs →
      Scans (fun field => EqualAt heap depth field needle) true xs out →
      ContainsAt heap depth needle target out
  | dictionary {address : Address} {out : Except Error (Option Entry)} :
      MembershipTarget.ofValue target = .dictionary address → DictionaryLookup heap address needle out →
      ContainsAt heap depth needle target (Option.isSome <$> out)

/-- Operator rules yield either a Boolean or the error from the reached test. -/
inductive Tests (heap : Heap) (left right : Value) : ComparisonOp → Except Error Bool → Prop where
  | eq {out : Except Error Bool} :
      EqualAt heap defaultDepth left right out → Tests heap left right .eq out
  | ne {out : Except Error Bool} :
      EqualAt heap defaultDepth left right out → Tests heap left right .ne ((! ·) <$> out)
  | mem {out : Except Error Bool} :
      ContainsAt heap defaultDepth left right out → Tests heap left right .mem out
  | notMem {out : Except Error Bool} :
      ContainsAt heap defaultDepth left right out → Tests heap left right .notMem ((! ·) <$> out)

end Silmaril.Languages.Starlark.Lists.Comparison
