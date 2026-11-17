module

public import Silmaril.Logic.SAT.LRAT.Defs
public import Mathlib.Data.Set.Defs

@[expose] public section

/-!
# CNF carriers of 32-bit words: problem languages and certificate-checking acceptors

Two ways to send a CNF formula as WIT values of type `s32`, and the problem languages they
carry. Both are read into the existing formulas `Silmaril.Logic.SAT.CNF` (no new CNF
formalism); the existing DIMACS reader `Dimacs.cnf` is the stream reading.

## Words

A **word** (`S32 := BitVec 32`) is a WIT `s32` value, which is the core `i32` of the canonical
ABI: a 32-bit pattern read in two's complement (`BitVec.toInt`, range `[-2³¹, 2³¹)`). A word is a
**literal word** (`LitWord`) when it is neither `0` (the DIMACS terminator, which is also its
own negation) nor `Int32.MIN = -2³¹` (`BitVec.intMin 32`, whose negation `2³¹` is not an `s32`
and whose variable `2³¹` has no positive literal word). The literal of a literal word `x` is
`x.toInt`, a nonzero integer with `|x.toInt| < 2³¹`. Conversely `encodeLit l` is the word
`BitVec.ofInt 32 l`, which is `l` back exactly when `LitRange l` (`l ≠ 0`, `|l| < 2³¹`).

## The two problem carriers

* **Nested** (`Nested := List (List S32)`, WIT `list<list<s32>>`): one inner list per clause.
  `decodeNested p` is `some F` when every word of every clause is a literal word, and then `F`
  is `p` read word by word; otherwise `none`. A `0` inside a clause is **malformed** (it is
  never read as a terminator, and the clause is never split). `[]` is the empty formula
  (satisfiable) and `[[]]` the formula with one empty clause (unsatisfiable).
* **Zero-terminated stream** (`Stream := List S32`, WIT `list<s32>`): DIMACS clause bodies, each
  clause followed by `0`. `decodeStream xs` is `some (Dimacs.cnf (xs.map toInt))` when no word
  is `Int32.MIN` and the stream is empty or ends with `0` (`StreamOk`); otherwise `none`. An
  unterminated last clause is **malformed**: it is neither dropped nor closed implicitly.
  `[]` is the empty formula and `[0]` the formula `[[]]`.

Malformed input is `none`, never the empty formula: `decodeNested [[0]] = none`,
`decodeStream [1] = none`, while `decodeNested [] = some []` (`…Carrier.Examples`).

## Problem languages

`UnsatNested`, `SatNested`, `UnsatStream`, `SatStream`: the inputs that decode to an
unsatisfiable (resp. satisfiable) formula. Malformed inputs are in neither language.

## Certificate-checking acceptors

An executable acceptor is a Boolean check of a problem and a certificate,
`chk : α → β → Bool`; the problem language it accepts is the existential projection
`Accepts chk = {p | ∃ c, chk p c = true}`. A **sound** acceptor for a language `L` has
`Accepts chk ⊆ L`; nothing here claims completeness or a decision procedure.

* **UNSAT**, by LRAT: `lratNested p c` and `lratStream p c` decode the problem and the flat
  LRAT certificate stream `c` (`LratStream.decode`, below) and run the reference checker
  `LRAT.check`; malformed problems or certificates are rejected.
* **SAT**, by a model: `satNested p m` and `satStream p m` decode the problem and check the
  model witness `m : List S32` (`modelOk`): every word of `m` is a literal word, no literal
  occurs with its negation (consistency), and every clause contains a literal of `m`. A SAT
  answer is never the negation of an UNSAT answer, nor an exit status: it is this check of
  an explicit witness.

## The flat LRAT certificate stream (version 1)

A certificate is a list of words (WIT `list<s32>`), a sequence of steps, each starting with a
tag word:

| step | words |
|---|---|
| `add id lits hints` (RUP) | `1, id, l₁, …, lₖ, 0, h₁, …, hₘ, 0` |
| `del ids` | `2, i₁, …, iₘ, 0` |
| `rat id lits groups` | `3, id, l₁, …, lₖ, 0, (j, h₁, …, hₘ, 0)*, 0` |

Ids, hints and RAT candidate ids `j` are positive words (`1 ≤ · < 2³¹`), literals are literal
words. In a RAT step each group is its candidate id followed by its own RUP hints and `0`; the
group list ends with an extra `0` (a candidate id is never `0`). Any other word in tag position,
a nonpositive id, a non-literal word in a literal position, or a stream ending inside a step is
malformed (`none`), and the acceptors reject it. Steps whose ids or hints are `0` or `≥ 2³¹`, or
whose literals are not `LitRange`, are not representable (`LratStream.StepRange`); decoding is
lossless on the representable steps (`LratStream.decode_encode`, `LratStream.encode_decode`).

A Silmaril addition.
-/

namespace Silmaril.Logic.SAT.Carrier

/-! ## Words -/

/-- A WIT `s32` value (the core `i32`), read in two's complement by `BitVec.toInt`. -/
abbrev S32 := BitVec 32

/-- A literal word: neither the terminator `0` nor `Int32.MIN = -2³¹`. -/
def LitWord (x : S32) : Bool := x != 0 && x != BitVec.intMin 32

/-- An integer that a word represents exactly and that is not `Int32.MIN`: `|l| < 2³¹`. -/
def InRange (l : Int) : Prop := -2 ^ 31 < l ∧ l < 2 ^ 31

instance (l : Int) : Decidable (InRange l) := inferInstanceAs (Decidable (_ ∧ _))

/-- An integer literal that a literal word represents exactly: nonzero, with `|l| < 2³¹`. -/
def LitRange (l : Lit) : Prop := l ≠ 0 ∧ InRange l

instance (l : Lit) : Decidable (LitRange l) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every literal of every clause of `F` is in range. -/
def CnfRange (F : CNF) : Prop := ∀ C ∈ F, ∀ l ∈ C, LitRange l

/-- The word of an integer (two's complement, modulo `2³²`). -/
def encodeLit (l : Lit) : S32 := BitVec.ofInt 32 l

/-! ## The nested carrier -/

/-- A CNF formula as `list<list<s32>>`: one inner list per clause. -/
abbrev Nested := List (List S32)

/-- **The nested reading**: every word of every clause is read as its literal, when all of them
are literal words; `none` on any `0` or `Int32.MIN`. -/
def decodeNested (p : Nested) : Option CNF :=
  if p.all (·.all LitWord) then some (p.map (·.map BitVec.toInt)) else none

/-- The nested words of a formula. -/
def encodeNested (F : CNF) : Nested := F.map (·.map encodeLit)

/-! ## The zero-terminated stream carrier -/

/-- A CNF formula as `list<s32>`: DIMACS clause bodies, each followed by `0`. -/
abbrev Stream := List S32

/-- A well-formed stream: no `Int32.MIN`, and empty or ending with the terminator `0`. -/
def StreamOk (xs : Stream) : Bool :=
  xs.all (· != BitVec.intMin 32) && xs.getLast?.all (· == 0)

/-- **The stream reading**: the existing DIMACS reading of the signed words, when the stream is
well formed (`StreamOk`); `none` otherwise. -/
def decodeStream (xs : Stream) : Option CNF :=
  if StreamOk xs then some (Dimacs.cnf (xs.map BitVec.toInt)) else none

/-- The stream of a formula: the words of its DIMACS stream (`Dimacs.write`). -/
def encodeStream (F : CNF) : Stream := (Dimacs.write F).map encodeLit

/-- The stream of a nested input: each inner list followed by the terminator `0`. -/
def flatten (p : Nested) : Stream := p.flatMap (· ++ [0])

/-! ## Problem languages -/

/-- Nested inputs of unsatisfiable formulas. -/
def UnsatNested : Set Nested := {p | ∃ F, decodeNested p = some F ∧ F.Unsat}

/-- Nested inputs of satisfiable formulas. -/
def SatNested : Set Nested := {p | ∃ F, decodeNested p = some F ∧ F.Sat}

/-- Streams of unsatisfiable formulas. -/
def UnsatStream : Set Stream := {xs | ∃ F, decodeStream xs = some F ∧ F.Unsat}

/-- Streams of satisfiable formulas. -/
def SatStream : Set Stream := {xs | ∃ F, decodeStream xs = some F ∧ F.Sat}

/-! ## Acceptors -/

/-- **The problems a certificate checker accepts**: those with some accepted certificate. -/
def Accepts {α β : Type} (chk : α → β → Bool) : Set α := {p | ∃ c, chk p c = true}

/-! ## The flat LRAT certificate stream -/

namespace LratStream

/-- A positive word as a natural number (an id or a hint). -/
def posWord? (x : S32) : Option Nat := if 0 < x.toInt then some x.toInt.toNat else none

/-- Literal words up to the terminator `0`, and the rest after it. -/
def lits : List S32 → Option (Clause × List S32)
  | [] => none
  | x :: xs =>
    if x = 0 then some ([], xs)
    else if LitWord x then (lits xs).map fun r => (x.toInt :: r.1, r.2)
    else none

/-- Positive words up to the terminator `0`, and the rest after it. -/
def ids : List S32 → Option (List Nat × List S32)
  | [] => none
  | x :: xs =>
    if x = 0 then some ([], xs)
    else (posWord? x).bind fun n => (ids xs).map fun r => (n :: r.1, r.2)

/-- RAT groups `(j, h₁, …, hₘ, 0)*` up to the extra terminator `0` (`fuel` bounds the number of
groups). -/
def groups : Nat → List S32 → Option (List (Nat × List Nat) × List S32)
  | _, [] => none
  | 0, _ :: _ => none
  | f + 1, x :: xs =>
    if x = 0 then some ([], xs)
    else (posWord? x).bind fun j => (ids xs).bind fun q =>
      (groups f q.2).map fun q' => ((j, q.1) :: q'.1, q'.2)

/-- One step, from its tag word (`fuel` bounds the number of RAT groups). -/
def step (fuel : Nat) : List S32 → Option (LRAT.Step × List S32)
  | t :: x :: xs =>
    if t = 1 then
      (posWord? x).bind fun id => (lits xs).bind fun q =>
        (ids q.2).map fun q' => (.add id q.1 q'.1, q'.2)
    else if t = 2 then
      (ids (x :: xs)).map fun q => (.del q.1, q.2)
    else if t = 3 then
      (posWord? x).bind fun id => (lits xs).bind fun q =>
        (groups fuel q.2).map fun q' => (.rat id q.1 q'.1, q'.2)
    else none
  | _ => none

/-- Steps until the stream is exhausted (`fuel` bounds the number of steps; each step gets the
length of the rest as its group fuel). -/
def steps : Nat → List S32 → Option (List LRAT.Step)
  | _, [] => some []
  | 0, _ :: _ => none
  | f + 1, x :: xs =>
    (step (x :: xs).length (x :: xs)).bind fun q => (steps f q.2).map (q.1 :: ·)

/-- **The decoder** of the flat LRAT certificate stream: `none` on malformed input. -/
def decode (xs : List S32) : Option (List LRAT.Step) := steps xs.length xs

/-- The word of a natural number (an id or a hint). -/
def natWord (n : Nat) : S32 := BitVec.ofNat 32 n

/-- The words of `ls ++ [0]`. -/
def encLits (ls : Clause) : List S32 := ls.map encodeLit ++ [0]

/-- The words of `is ++ [0]`. -/
def encIds (is : List Nat) : List S32 := is.map natWord ++ [0]

/-- The words of RAT groups: each candidate id and its hints, then the extra terminator. -/
def encGroups (gs : List (Nat × List Nat)) : List S32 :=
  gs.flatMap (fun g => natWord g.1 :: encIds g.2) ++ [0]

/-- The words of one step. -/
def encodeStep : LRAT.Step → List S32
  | .add id ls hs => [1, natWord id] ++ encLits ls ++ encIds hs
  | .del is => 2 :: encIds is
  | .rat id ls gs => [3, natWord id] ++ encLits ls ++ encGroups gs

/-- **The encoder**: the steps' words in order. -/
def encode (ss : List LRAT.Step) : List S32 := ss.flatMap encodeStep

/-- An id or hint that a positive word represents: `1 ≤ n < 2³¹`. -/
def NatRange (n : Nat) : Prop := 0 < n ∧ n < 2 ^ 31

/-- A representable step: positive ids, hints and candidates below `2³¹`, literals in range. -/
def StepRange : LRAT.Step → Prop
  | .add id ls hs => NatRange id ∧ (∀ l ∈ ls, LitRange l) ∧ ∀ h ∈ hs, NatRange h
  | .del is => ∀ i ∈ is, NatRange i
  | .rat id ls gs => NatRange id ∧ (∀ l ∈ ls, LitRange l) ∧
      ∀ g ∈ gs, NatRange g.1 ∧ ∀ h ∈ g.2, NatRange h

end LratStream

/-! ## The acceptors -/

/-- **LRAT acceptor, nested problems**: decode both, run `LRAT.check`. -/
def lratNested (p : Nested) (c : List S32) : Bool :=
  match decodeNested p, LratStream.decode c with
  | some F, some ss => LRAT.check F ss
  | _, _ => false

/-- **LRAT acceptor, zero-terminated streams.** -/
def lratStream (xs : Stream) (c : List S32) : Bool :=
  match decodeStream xs, LratStream.decode c with
  | some F, some ss => LRAT.check F ss
  | _, _ => false

/-- The assignment of a model witness: a variable is true when its positive literal is listed. -/
def modelAsg (m : List S32) : Assignment := fun v => (m.map BitVec.toInt).contains (v : Int)

/-- **The model check**: literal words only, consistent (no literal with its negation), and
every clause contains a listed literal. -/
def modelOk (F : CNF) (m : List S32) : Bool :=
  let M := m.map BitVec.toInt
  m.all LitWord && M.all (fun l => !M.contains (-l)) && F.all (·.any M.contains)

/-- **SAT acceptor, nested problems**: decode, check the model witness. -/
def satNested (p : Nested) (m : List S32) : Bool :=
  match decodeNested p with
  | some F => modelOk F m
  | none => false

/-- **SAT acceptor, zero-terminated streams.** -/
def satStream (xs : Stream) (m : List S32) : Bool :=
  match decodeStream xs with
  | some F => modelOk F m
  | none => false

end Silmaril.Logic.SAT.Carrier
