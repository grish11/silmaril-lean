module

/-!
# Shared ASCII S-expression reader

Atoms, parentheses, whitespace and semicolon comments are read in two structural
passes over a byte list. Outside comments, non-ASCII bytes, string quotes and
quoted-symbol bars reject. Comments skip arbitrary bytes until LF. This module contains no SMT sorts, terms, evaluator or command decoder.
The declarations retain their existing `Silmaril.Logic.Smt` names so legacy and
sorted frontends share the same syntax and reader.
-/

@[expose] public section

namespace Silmaril.Logic.Smt

/-- Decimal digits, most significant first; `none` if empty or not all digits. -/
def digits (base : Nat) (val : Char → Option Nat) : List Char → Option Nat
  | [] => none
  | cs => cs.foldl (fun acc c => acc.bind fun a => (val c).map (a * base + ·)) (some 0)

def decVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat) else none

/-- Lexical tokens. -/
inductive Tok where
  | lp
  | rp
  | atom (s : String)

/-- S-expressions: atoms and lists. -/
inductive SE where
  | atom (s : String)
  | list (xs : List SE)

namespace SE

mutual

/-- Constructive structural equality for the nested tree representation. Lean's
`DecidableEq` deriving handler does not support recursive occurrences under List. -/
def decEq : (a b : SE) → Decidable (a = b)
  | .atom x, .atom y =>
      if h : x = y then .isTrue (congrArg SE.atom h)
      else .isFalse (fun equal => h (SE.atom.inj equal))
  | .atom _, .list _ => .isFalse (by intro equal; cases equal)
  | .list _, .atom _ => .isFalse (by intro equal; cases equal)
  | .list xs, .list ys =>
      match decEqList xs ys with
      | .isTrue h => .isTrue (congrArg SE.list h)
      | .isFalse h => .isFalse (fun equal => h (SE.list.inj equal))

/-- The list component of structural S-expression equality. -/
def decEqList : (xs ys : List SE) → Decidable (xs = ys)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by intro equal; cases equal)
  | _ :: _, [] => .isFalse (by intro equal; cases equal)
  | x :: xs, y :: ys =>
      match decEq x y with
      | .isFalse h => .isFalse (fun equal => h (List.cons.inj equal).1)
      | .isTrue h =>
          match decEqList xs ys with
          | .isFalse h' => .isFalse (fun equal => h' (List.cons.inj equal).2)
          | .isTrue h' => .isTrue (by cases h; cases h'; rfl)

end

instance : DecidableEq SE := decEq

end SE

/-- End the current token. -/
def flush (cur : List Char) (acc : List Tok) : List Tok :=
  if cur.isEmpty then acc else .atom (String.ofList cur.reverse) :: acc

/-- Split bytes into tokens. `comment`: inside a `;` comment; `cur`: the current token,
reversed; `acc`: the tokens so far, reversed. -/
def lex : List UInt8 → (comment : Bool) → (cur : List Char) → (acc : List Tok) → Option (List Tok)
  | [], _, cur, acc => some (flush cur acc).reverse
  | b :: bs, true, cur, acc => lex bs (b.toNat != 10) cur acc
  | b :: bs, false, cur, acc =>
      let n := b.toNat
      if n == 59 then lex bs true [] (flush cur acc)                          -- ;
      else if n == 40 then lex bs false [] (.lp :: flush cur acc)            -- (
      else if n == 41 then lex bs false [] (.rp :: flush cur acc)            -- )
      else if n == 32 || n == 9 || n == 10 || n == 13 then lex bs false [] (flush cur acc)
      else if n ≥ 128 || n == 34 || n == 124 || n < 32 then none            -- non-ASCII, " |
      else lex bs false (Char.ofNat n :: cur) acc

/-- Build the forms from tokens. `stk`: the open lists, innermost first, each reversed; the last
one is the top level. -/
def build : List Tok → List (List SE) → Option (List SE)
  | [], [top] => some top.reverse
  | [], _ => none
  | .lp :: ts, stk => build ts ([] :: stk)
  | .rp :: ts, cur :: parent :: stk => build ts ((SE.list cur.reverse :: parent) :: stk)
  | .rp :: _, _ => none
  | .atom a :: ts, cur :: stk => build ts ((SE.atom a :: cur) :: stk)
  | .atom _ :: _, [] => none

/-- The forms of a byte string. -/
def readForms (bytes : List UInt8) : Option (List SE) :=
  lex bytes false [] [] >>= fun ts => build ts [[]]

end Silmaril.Logic.Smt
