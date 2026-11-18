module

public import Silmaril.Formats.SExp.Basic

/-!
# A shared reader for Lisp-family text syntaxes

Every Lisp-family text syntax in `Silmaril.Formats.SExp` (the dotted text format, Scheme,
Racket, Common Lisp, Clojure) is read by the same two layers:

* a **lexer** `next : σ → Step A C σ`, written once per dialect, which skips atmosphere
  (whitespace and comments) and returns the next token and the remaining input, or `eof`
  when only atmosphere remains, or `error`;
* the **phrase grammar** below, shared by all dialects: a datum is an atom, a bracketed
  sequence of data (possibly ending in a dot and a tail datum, when the bracket allows it),
  or a prefix (abbreviation) token followed by a datum.

The phrase grammar is the inductive relation `Gram`; the executable reader `datum` is proved
sound, complete and deterministic with respect to it (`Silmaril.Formats.SExp.Reader.Thms`).

## Datum encoding into `SExp2`

Data are read into the existing `SExp2 A` (no new tree type). A bracketed sequence is a cons
spine, nil-terminated unless a dot gave a tail. Dialect-specific collection syntax (a Scheme
vector `#(…)`, a Clojure vector `[…]`, map `{…}`, set `#{…}`) is encoded by a **marker atom**:
an atom `m` whose `Notation.role` is `coll`, placed at the head of the spine:
`#(a b)` ↦ `cons (atom vec) (cons a (cons b nil))`. A prefix whose datum has no longhand
list form (a Common Lisp backquote, a Racket box) is encoded likewise by a marker of role
`prefix`: `` `x `` ↦ `cons (atom bq) (cons x nil)`. Marker atoms are never produced by the lexer
as ordinary atoms, so the encoding is injective; `wf` characterizes its image (every reader
result is `wf`, and every `wf` datum is printed and read back exactly).

Abbreviations whose meaning *is* a list (`'x` is `(quote x)` in every dialect here) are read as
that list with an ordinary symbol head, as the standards specify; such data print in longhand.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Formats.SExpReader

universe u v

/-- Tokens of a Lisp-family syntax. `C` indexes the closing delimiters of the dialect. -/
inductive Token (A : Type u) (C : Type) where
  /-- An ordinary atom (symbol, number, string, …). -/
  | atom (value : A)
  /-- An opening delimiter: `head = none` for an ordinary list, `some m` for a collection
  encoded with marker `m`; `dotted` says whether the dot is allowed before the closer. -/
  | «open» (head : Option A) (closer : C) (dotted : Bool)
  | close (closer : C)
  /-- The consing dot of `(a . b)`. -/
  | dot
  /-- A prefix token whose following datum `x` reads as `(head x)`. -/
  | «prefix» (head : A)
  deriving DecidableEq, Repr

namespace Token
variable {A : Type u} {C : Type}

def isOpen : Token A C → Bool
  | .open .. => true
  | _ => false

def isClose : Token A C → Bool
  | .close _ => true
  | _ => false

def isPrefix : Token A C → Bool
  | .prefix _ => true
  | _ => false

/-- Tokens that can start a datum. -/
def startsDatum : Token A C → Bool
  | .atom _ | .open .. | .prefix _ => true
  | .close _ | .dot => false

end Token

/-- One lexer step. -/
inductive Step (A : Type u) (C : Type) (σ : Type v) where
  | token (t : Token A C) (rest : σ)
  /-- Only atmosphere (whitespace, comments) remains. -/
  | eof
  | error
  deriving DecidableEq, Repr

def Step.isEof {A : Type u} {C : Type} {σ : Type v} : Step A C σ → Bool
  | .eof => true
  | _ => false

/-- A lexer over states `σ` with a size that every token strictly decreases. -/
structure Lexer (A : Type u) (C : Type) (σ : Type v) where
  step : σ → Step A C σ
  size : σ → Nat

namespace Lexer
variable {A : Type u} {C : Type} {σ : Type v}

/-- The lexer step guarded by progress: a token that does not shrink the input is an error.
Guarding makes the reader total with a fuel bound computed from the input size. -/
def next (L : Lexer A C σ) (s : σ) : Step A C σ :=
  match L.step s with
  | .token t rest => if L.size rest < L.size s then .token t rest else .error
  | r => r

/-- `Emits L s ts s'`: from `s` the lexer produces exactly the tokens `ts` and stops at `s'`. -/
inductive Emits (L : Lexer A C σ) : σ → List (Token A C) → σ → Prop
  | nil (s : σ) : Emits L s [] s
  | cons {s s₁ s₂ : σ} {t : Token A C} {ts : List (Token A C)} :
      L.next s = .token t s₁ → Emits L s₁ ts s₂ → Emits L s (t :: ts) s₂

end Lexer

/-! ## The phrase grammar -/

/-- Grammar modes: a datum, or the remainder of a bracketed sequence with closer `c`, whether a
dot is allowed (`dotted`), and whether no element has been read yet (`first`). -/
inductive Mode (C : Type) where
  | datum
  | items (closer : C) (dotted first : Bool)
  deriving DecidableEq, Repr

variable {A : Type u} {C : Type}

/-- The datum of a bracketed sequence: its spine, behind the marker head if any. -/
def wrap : Option A → SExp2 A → SExp2 A
  | none, spine => spine
  | some m, spine => .cons (.atom m) spine

/-- **The phrase grammar** shared by all dialects: `Gram mode ts e` says the token string
`ts` derives `e` in `mode`. -/
inductive Gram : Mode C → List (Token A C) → SExp2 A → Prop
  | atom (a : A) : Gram .datum [.atom a] (.atom a)
  | coll (h : Option A) (c : C) (d : Bool) {ts : List (Token A C)} {e : SExp2 A} :
      Gram (.items c d true) ts e → Gram .datum (.open h c d :: ts) (wrap h e)
  | pre (p : A) {ts : List (Token A C)} {e : SExp2 A} :
      Gram .datum ts e → Gram .datum (.prefix p :: ts) (.cons (.atom p) (.cons e .nil))
  | close (c : C) (d first : Bool) : Gram (.items c d first) [.close c] .nil
  | dot (c : C) {ts : List (Token A C)} {e : SExp2 A} :
      Gram .datum ts e → Gram (.items c true false) (.dot :: ts ++ [.close c]) e
  | item (c : C) (d first : Bool) {ts us : List (Token A C)} {x r : SExp2 A} :
      Gram .datum ts x → Gram (.items c d false) us r →
      Gram (.items c d first) (ts ++ us) (.cons x r)

/-! ## The reader -/

section Reader
variable {σ : Type v} (L : Lexer A C σ) [DecidableEq C]

mutual
  /-- Read a datum whose first token `t` has been lexed already. -/
  def datumAfter : Nat → Token A C → σ → Option (SExp2 A × σ)
    | 0, _, _ => none
    | _ + 1, .atom a, s => some (.atom a, s)
    | n + 1, .open h c d, s => do
        let (e, s') ← items n c d true s
        some (wrap h e, s')
    | n + 1, .prefix p, s => do
        let (e, s') ← datum n s
        some (.cons (.atom p) (.cons e .nil), s')
    | _ + 1, .close _, _ => none
    | _ + 1, .dot, _ => none

  /-- Read one datum, returning the remaining input (prefix parsing). -/
  def datum : Nat → σ → Option (SExp2 A × σ)
    | 0, _ => none
    | n + 1, s =>
        match L.next s with
        | .token t s' => datumAfter n t s'
        | _ => none

  /-- Read the rest of a bracketed sequence up to and including its closer. -/
  def items : Nat → C → Bool → Bool → σ → Option (SExp2 A × σ)
    | 0, _, _, _, _ => none
    | n + 1, c, d, first, s =>
        match L.next s with
        | .token (.close c') s' => if c' = c then some (.nil, s') else none
        | .token .dot s' =>
            if d && !first then
              match datum n s' with
              | some (tail, s₂) =>
                  match L.next s₂ with
                  | .token (.close c') s₃ => if c' = c then some (tail, s₃) else none
                  | _ => none
              | none => none
            else none
        | .token t s' =>
            match datumAfter n t s' with
            | some (x, s₂) =>
                match items n c d false s₂ with
                | some (r, s₃) => some (.cons x r, s₃)
                | none => none
            | none => none
        | _ => none
end

/-- Fuel sufficient for any datum of input `s` (`Thms.read_iff`). -/
def fuel (s : σ) : Nat := 2 * L.size s + 2

/-- Read one datum from the front of `s`, returning the unconsumed input. -/
def readPrefix (s : σ) : Option (SExp2 A × σ) := datum L (fuel L s) s

/-- Read exactly one datum: after it only atmosphere may remain. -/
def read (s : σ) : Option (SExp2 A) :=
  match readPrefix L s with
  | some (e, rest) => if (L.next rest).isEof then some e else none
  | none => none

/-- Read a whole document: a sequence of data separated by atmosphere. -/
def readAllFuel : Nat → σ → Option (List (SExp2 A))
  | 0, _ => none
  | n + 1, s =>
      match L.next s with
      | .eof => some []
      | .error => none
      | .token _ _ =>
          match readPrefix L s with
          | some (e, rest) => (e :: ·) <$> readAllFuel n rest
          | none => none

def readAll (s : σ) : Option (List (SExp2 A)) := readAllFuel L (L.size s + 1) s

end Reader

/-! ## Notation: marker roles, well-formed data and their tokens -/

/-- The role of an atom in a dialect's encoding. -/
inductive Role (C : Type) where
  /-- An ordinary atom, written as an atom token. -/
  | plain
  /-- A collection marker: written as the opening token of a bracketed sequence. -/
  | coll (closer : C) (dotted : Bool)
  /-- A prefix marker: `cons (atom m) (cons x nil)` is written as the prefix token, then `x`. -/
  | «prefix»
  /-- An atom with no written form in the dialect (e.g. a Clojure symbol whose name breaks the
  symbol grammar, which Clojure cannot escape). No datum containing it is `wf`. -/
  | unwritable
  deriving DecidableEq, Repr

def Role.isPlain {C : Type} : Role C → Bool
  | .plain => true
  | _ => false

/-- How a dialect encodes its syntax in `SExp2`. -/
structure Notation (A : Type u) (C : Type) where
  role : A → Role C
  /-- The closer of ordinary lists. -/
  listCloser : C
  /-- Whether ordinary lists admit the dot (false for Clojure). -/
  listDotted : Bool

namespace Notation
variable (N : Notation A C)

/-- A lexer token respects the notation: plain atoms only as atom tokens, markers only as the
head of their own opening or prefix token. A prefix token may also carry a plain head: an
abbreviation such as `'x`, which reads as the ordinary list `(quote x)`. -/
def TokenOK : Token A C → Prop
  | .atom a => N.role a = .plain
  | .open none _ d => d = true → N.listDotted = true
  | .open (some m) c d => N.role m = .coll c d
  | .prefix p => N.role p = .prefix ∨ N.role p = .plain
  | .close _ | .dot => True

/-- Some bracket of the notation admits the dot. -/
def Dotted : Prop := N.listDotted = true ∨ ∃ m c, N.role m = .coll c true

mutual
  /-- The data with a written form: the image of the reader (`Thms.wf_of_gram`). -/
  def wf : SExp2 A → Bool
    | .nil => true
    | .atom a => (N.role a).isPlain
    | .cons (.atom m) r =>
        match N.role m with
        | .plain => wfItems N.listDotted false r
        | .coll _ d => wfItems d true r
        | .prefix => r.cdr.isNil && wfHead r
        | .unwritable => false
    | .cons x r => wf x && wfItems N.listDotted false r

  /-- `wf` of the first element. -/
  def wfHead : SExp2 A → Bool
    | .cons y _ => wf y
    | _ => false

  /-- Well-formed remainders of a bracketed sequence: a spine of well-formed elements, ending in
  `nil`, or (when `d` and not `first`) in a dotted tail: a plain atom or a marker-headed datum
  (`(a . #(b))` has a vector as its tail, which the spine encoding must not confuse with the
  elements `#` `(b)`). -/
  def wfItems (d first : Bool) : SExp2 A → Bool
    | .nil => true
    | .atom a => d && !first && (N.role a).isPlain
    | .cons (.atom m) r =>
        match N.role m with
        | .plain => wfItems d false r
        | .coll _ d' => d && !first && wfItems d' true r
        | .prefix => d && !first && r.cdr.isNil && wfHead r
        | .unwritable => false
    | .cons x r => wf x && wfItems d false r
end

mutual
  /-- The tokens that write a well-formed datum. Ordinary lists use the dialect's list closer;
  dotted tails are written with the dot. -/
  def tokens : SExp2 A → List (Token A C)
    | .nil => [.open none N.listCloser N.listDotted, .close N.listCloser]
    | .atom a => [.atom a]
    | .cons (.atom m) r =>
        match N.role m with
        | .plain => .open none N.listCloser N.listDotted :: .atom m :: itemTokens N.listCloser r
        | .coll c d => .open (some m) c d :: itemTokens c r
        | .prefix => .prefix m :: headTokens r
        | .unwritable => []
    | .cons x r => .open none N.listCloser N.listDotted :: tokens x ++ itemTokens N.listCloser r

  def itemTokens (c : C) : SExp2 A → List (Token A C)
    | .nil => [.close c]
    | .atom a => [.dot, .atom a, .close c]
    | .cons (.atom m) r =>
        match N.role m with
        | .plain => .atom m :: itemTokens c r
        | .coll c' d' => .dot :: .open (some m) c' d' :: itemTokens c' r ++ [.close c]
        | .prefix => .dot :: .prefix m :: headTokens r ++ [.close c]
        | .unwritable => []
    | .cons x r => tokens x ++ itemTokens c r

  /-- The tokens of the first element. -/
  def headTokens : SExp2 A → List (Token A C)
    | .cons y _ => tokens y
    | _ => []
end

end Notation

/-! ## Rendering tokens as text -/

/-- Separator between consecutive tokens: none after an opener or before a closer (unless the
closer follows a prefix), one space otherwise. -/
def sep (t u : Token A C) : List Char :=
  if t.isOpen || (u.isClose && !t.isPrefix) then [] else [' ']

/-- Render tokens, given the text of each token. -/
def render (text : Token A C → List Char) : List (Token A C) → List Char
  | [] => []
  | [t] => text t
  | t :: u :: ts => text t ++ sep t u ++ render text (u :: ts)

/-- What may follow an atom or dot in rendered text: the end, a space, or a closer. -/
def Follows (text : Token A C → List Char) (rest : List Char) : Prop :=
  rest = [] ∨ (∃ r, rest = ' ' :: r) ∨ (∃ c r, rest = text (.close c) ++ r)

/-- The obligations a dialect discharges to obtain the generic roundtrip theorem: each token
of a well-formed datum is lexed back from its text. -/
structure PrintLaws (N : Notation A C) (L : Lexer A C (List Char))
    (text : Token A C → List Char) : Prop where
  size_eq : ∀ s, L.size s = s.length
  space : ∀ s, L.step (' ' :: s) = L.step s
  eof : L.step [] = .eof
  /-- Atoms and the dot need a delimiter after them. -/
  atom : ∀ a rest, N.role a = .plain → Follows text rest →
    L.step (text (.atom a) ++ rest) = .token (.atom a) rest
  dot : N.Dotted → ∀ rest, Follows text rest → L.step (text .dot ++ rest) = .token .dot rest
  openList : ∀ rest, L.step (text (.open none N.listCloser N.listDotted) ++ rest) =
    .token (.open none N.listCloser N.listDotted) rest
  openColl : ∀ m c d rest, N.role m = .coll c d →
    L.step (text (.open (some m) c d) ++ rest) = .token (.open (some m) c d) rest
  close : ∀ c rest, L.step (text (.close c) ++ rest) = .token (.close c) rest
  «prefix» : ∀ p rest, N.role p = .prefix →
    L.step (text (.prefix p) ++ ' ' :: rest) = .token (.prefix p) (' ' :: rest)
  /-- Every token text is nonempty. -/
  nonempty : ∀ t, text t ≠ []

/-- Print a well-formed datum. -/
def print (N : Notation A C) (text : Token A C → List Char) (e : SExp2 A) : List Char :=
  render text (N.tokens e)

end Silmaril.Formats.SExpReader
