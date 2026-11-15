module

public import Silmaril.Semantics.Acceptors.Defs
public import Silmaril.Semantics.StreamMonitors.Defs

/-!
# Resource bounds for streaming languages

Generic bounds on the inputs of a streaming acceptor, with no format specifics. Three kinds
of bound are kept apart, because they behave differently on unbounded streams:

* a **whole-input bound**: the total length is at most `n` (`RunBound List.length n`);
* a **per-item bound**: every item between separators has at most `n` symbols
  (`ItemBound isSep n`), as for JSON Lines, where a stream may carry unboundedly many
  bounded items;
* a **depth bound**: the nesting depth over a token alphabet whose tokens are classified
  as opening, closing or neutral is at most `d` (`DepthBound kind d`). This is generic
  bracket structure, not the grammar of any format.

All three are instances of one construction. `RunBound f n` is the language of words all
of whose prefixes `p` have running measure `f p ≤ n`. It is prefix-closed by construction,
so its infinite counterpart `safetyω (RunBound f n)` is a safety property.

## Completeness relative to a bound

`Acceptor.CorrectFold` from `Silmaril.Semantics.Acceptors` splits into two halves:

* `Acceptor.SoundFold A L`: a yes answer after any chunk list means the input is in `L`;
* `Acceptor.CompleteFoldOn A L B`: every input in `L ∩ B` gets a yes answer.

Soundness is unbounded. Completeness is stated relative to an explicit *bound language*
`B`; `B = Set.univ` is full completeness. Nothing in streaming semantics forces `B` to be
a bound: a streaming acceptor may be complete on inputs of every length. When an
implementation is only complete within a resource bound, that bound is the parameter `B`,
not a hidden fact. `Acceptor.boundedReference L B` is the reference acceptor that answers
membership of `L ∩ B`: sound for `L`, complete on `B`.

## Resource and ABI assumptions

The following are distinct and are each stated as a parameter or a hypothesis where they
are used. None is a proved fact about an implementation.

* **Per-chunk transport limits.** `ChunkBound k cs` says that every chunk has at most `k`
  symbols. A host ABI may impose such a limit per `process` call; for instance WIT
  `list<u8>` arguments have canonical-ABI lengths that are 32-bit in wasm32. Here `k` is
  only a parameter. A transport limit does not restrict the delivered language: for
  `k ≥ 1` every finite and every infinite word is the limit of a `ChunkBound k` stream
  (`Thms`).
* **Acceptor state memory.** Not modelled. A bounded-state acceptor can only be complete on
  a language it can recognise with that state; characterising those languages is out of
  scope.
* **Whole-input bounds** (`RunBound List.length n`). No infinite word satisfies one.
* **Per-item bounds** (`ItemBound isSep n`). Satisfiable by infinite words whose
  separators recur, so an unbounded number of bounded items is a nonempty safety property
  while the total length is unbounded.
* **Depth bounds** (`DepthBound kind d`). A word that only opens leaves every depth bound,
  so bounded-depth completeness says nothing about it.

## Scope

These are statements about languages and chunk streams. Nothing here proves anything
about the execution of a concrete Wasm component or any other program.
-/

@[expose] public section

namespace Silmaril.Streams

open Cslib

universe u v

variable {α : Type u} {τ : Type v}

/-- Words all of whose prefixes have running measure at most `n`. -/
def RunBound (f : List α → ℕ) (n : ℕ) : Language α := {w | ∀ p, p <+: w → f p ≤ n}

/-- The number of symbols since the last separator, computed left to right: a separator
resets the count to `0`, any other symbol adds one. -/
def gap (isSep : α → Bool) (w : List α) : ℕ :=
  w.foldl (fun k a => if isSep a then 0 else k + 1) 0

/-- Per-item bound: every item (maximal run of non-separators) has at most `n` symbols. -/
def ItemBound (isSep : α → Bool) (n : ℕ) : Language α := RunBound (gap isSep) n

/-- How a token affects nesting depth. -/
inductive BracketKind where
  /-- An opening bracket: depth goes up by one. -/
  | opening
  /-- A closing bracket: depth goes down by one, floored at `0`. -/
  | closing
  /-- Any other token: depth is unchanged. -/
  | neutral
  deriving DecidableEq, Repr

/-- One step of the truncated nesting depth. -/
def depthStep (kind : τ → BracketKind) (d : ℕ) (t : τ) : ℕ :=
  match kind t with
  | .opening => d + 1
  | .closing => d - 1
  | .neutral => d

/-- The nesting depth after reading `w` from depth `0`, with unmatched closes floored at `0`. -/
def depth (kind : τ → BracketKind) (w : List τ) : ℕ := w.foldl (depthStep kind) 0

/-- Depth bound: the nesting depth never exceeds `d`. -/
def DepthBound (kind : τ → BracketKind) (d : ℕ) : Language τ := RunBound (depth kind) d

/-- The signed contribution of a token to the nesting depth. -/
def bracketDelta (kind : τ → BracketKind) (t : τ) : ℤ :=
  match kind t with
  | .opening => 1
  | .closing => -1
  | .neutral => 0

/-- Opens minus closes, without truncation. -/
def netDepth (kind : τ → BracketKind) (w : List τ) : ℤ := (w.map (bracketDelta kind)).sum

/-- Balanced bracket structure: no prefix closes more than it opens, and the word as a
whole closes everything it opens. -/
def Balanced (kind : τ → BracketKind) : Language τ :=
  {w | (∀ p, p <+: w → 0 ≤ netDepth kind p) ∧ netDepth kind w = 0}

/-- A per-chunk transport limit: every chunk carries at most `k` symbols. -/
def ChunkBound (k : ℕ) (cs : Chunks α) : Prop := ∀ n, (cs n).length ≤ k

/-- The infinite word repeating `item ++ [sep]` forever. -/
def repeatItem (item : List α) (sep : α) : ωSequence α :=
  fun i => (item ++ [sep]).getD (i % (item.length + 1)) sep

end Silmaril.Streams

namespace Silmaril.Acceptor

universe w x y

variable {σ : Type w} {χ : Type x} {α : Type y}

variable [ChunkView χ α]

/-- Soundness for chunk-list inputs: a yes answer after processing `cs` means the delivered
symbols are in `L`. -/
def SoundFold (A : Acceptor σ χ) (L : Language α) : Prop :=
  ∀ cs : List χ, (A.query (cs.foldl A.process A.init)).1 = true →
    cs.flatMap ChunkView.toList ∈ L

/-- Completeness relative to a bound language `B`: every chunk list whose symbols are in
`L ∩ B` gets a yes answer. Inputs outside `B` are unconstrained. -/
def CompleteFoldOn (A : Acceptor σ χ) (L B : Language α) : Prop :=
  ∀ cs : List χ, cs.flatMap ChunkView.toList ∈ L → cs.flatMap ChunkView.toList ∈ B →
    (A.query (cs.foldl A.process A.init)).1 = true

/-- Membership of an intersection of decidable languages is decidable. -/
instance instDecidableMemInf (L B : Language α) [DecidablePred (· ∈ L)] [DecidablePred (· ∈ B)] :
    DecidablePred (· ∈ L ⊓ B) :=
  fun w => decidable_of_iff (w ∈ L ∧ w ∈ B) Language.mem_inf.symm

/-- The bounded reference acceptor: remember the input and answer membership of `L ∩ B`. -/
def boundedReference (L B : Language α) [DecidablePred (· ∈ L)] [DecidablePred (· ∈ B)] :
    Acceptor (List α) χ where
  init := []
  process w c := w ++ ChunkView.toList c
  query w := (member L w && member B w, w)
  reset _ := []

end Silmaril.Acceptor
