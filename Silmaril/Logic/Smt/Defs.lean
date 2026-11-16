module

public import Silmaril.Logic.Smt.SExpr.Defs


/-!
# SMT-LIB v2 scripts: a small fragment and its denotation

An SMT-LIB v2 script is read in two steps: a small S-expression reader over bytes
(`readForms : List UInt8 → Option (List SE)`, a script being a sequence of forms), then
`decodeScript : List SE → Option Script`. `Script.ofBytes?` is the composition and
`Script.parse?` its version on text. The denotation is a predicate over assignments:

* `Script.Holds s ρ`: the model `ρ : Model` gives every declared symbol a value of its sort, and
  every assertion evaluates to `true`;
* `Script.Sat s := ∃ ρ, s.Holds ρ` (the SMT answer `sat`), and `¬ s.Sat` (`unsat`);
* `Script.Expected s`: the script's own `(set-info :status …)` is correct.

**Fragment.**
* Commands: `set-logic`, `set-info`, `declare-const`, `declare-fun` with no arguments,
  `assert`, `check-sat`, `exit`, and the no-ops `set-option`, `get-model`, `get-info`,
  `get-value`, `get-assertions`, `echo`. At most one `check-sat`, and no `declare-*` or
  `assert` after it. Symbols are declared once.
* Sorts: `Bool`, `Int`, `(_ BitVec w)`.
* Terms: symbols, `true`, `false`, numerals, `#b…`, `#x…`, `(_ bvN w)`, and the operators of
  `Op`: core (`not and or => xor = distinct ite`), Ints (`+ - * <= < >= > div mod abs`) and
  bit-vectors (`bvadd bvsub bvmul bvneg bvand bvor bvxor bvnot bvshl bvlshr bvult bvule bvugt
  bvuge bvslt bvsle bvsgt bvsge concat`).
* Lexical: ASCII only; `;` comments; no string literals and no `|quoted|` symbols.
* Anything else (`let`, quantifiers, `define-fun`, `push`/`pop`, other operators or sorts)
  makes the reader or the decoder return `none`; it never guesses.

**Well-sortedness.** The decoder accepts a script only if every assertion evaluates to a Boolean
under the default model (`Script.defaultModel`). The theorems in
`Silmaril.Logic.Smt.Sorting.Thms` prove that changing declared values while preserving their
sorts preserves evaluation failure and the sort of successful results. In particular,
`Script.eval_bool_ofBytes` proves that every accepted assertion evaluates to a Boolean under
every declaration-respecting assignment. Its truth value may change with the assignment.

**Semantic choices.** Bit-vectors are `Nat`s below `2 ^ w` (`Val.bv w n`), so the kernel
computes them with its `Nat` acceleration; the operations follow SMT-LIB's `FixedSizeBitVectors`
theory. `div`/`mod` are Lean's `Int.ediv`/`Int.emod`, which agree with SMT-LIB's Euclidean
division for a nonzero divisor. At zero the fixed choices are `a div 0 = 0`
and `a mod 0 = a`, whereas SMT-LIB leaves those operations unspecified (a known gap: a script whose answer depends on `x div 0` can differ).

**Kernel discipline.** Every function is structurally recursive, the reader walks the byte
list once (no indexing), and operators are decoded once into the enumeration `Op`, so
`decide +kernel` can read, decode and evaluate small scripts. The kernel has no fast `String`,
`ByteArray` or `Array`: keep kernel-checked scripts small (the costs of the examples are in
`Silmaril.Project.Formats.Smt.Thms`).

A Silmaril addition (`notes/silmaril-projects/v0.md` §17).
-/

@[expose] public section

namespace Silmaril.Logic.Smt

/-- The sorts of the fragment. -/
inductive Ty where
  | bool
  | int
  | bv (w : Nat)
  deriving DecidableEq, Repr

/-- Values. A bit-vector of width `w` is a `Nat` below `2 ^ w`. -/
inductive Val where
  | bool (b : Bool)
  | int (i : Int)
  | bv (w : Nat) (n : Nat)
  deriving DecidableEq, Repr

/-- The operators of the fragment. -/
inductive Op where
  | not | and | or | imp | xor | eq | distinct | ite
  | add | sub | mul | le | lt | ge | gt | div | mod | abs
  | bvadd | bvsub | bvmul | bvneg | bvand | bvor | bvxor | bvnot | bvshl | bvlshr
  | bvult | bvule | bvugt | bvuge | bvslt | bvsle | bvsgt | bvsge | concat
  deriving DecidableEq, Repr

mutual
/-- Terms. -/
inductive Term where
  | var (x : String)
  | bool (b : Bool)
  | int (n : Nat)
  | bv (w n : Nat)
  | app (op : Op) (args : Args)
/-- Argument lists. A mutual list type rather than `List Term`, because Lean derives
`DecidableEq` for mutual inductives but not for nested ones. -/
inductive Args where
  | nil
  | cons (t : Term) (ts : Args)
end
deriving instance DecidableEq, Repr for Term, Args

/-- Arguments from a list. -/
def Args.ofList : List Term → Args
  | [] => .nil
  | t :: ts => .cons t (Args.ofList ts)

/-- Commands. `ignored` keeps the name of a command without logical content. -/
inductive Cmd where
  | setLogic (l : String)
  | setInfo (k v : String)
  | declare (x : String) (σ : Ty)
  | assert (t : Term)
  | checkSat
  | exit
  | ignored (c : String)
  deriving DecidableEq, Repr

/-- A script: its commands, in order. -/
structure Script where
  cmds : List Cmd
  deriving DecidableEq, Repr

/-- An assignment of values to symbols. -/
abbrev Model := String → Val

/-! ## Values -/

namespace Val

/-- The sort of a value. -/
def sort : Val → Ty
  | .bool _ => .bool
  | .int _ => .int
  | .bv w _ => .bv w

/-- `v` is a value of sort `σ` (for bit-vectors: the right width, and in range). -/
def hasSort : Val → Ty → Bool
  | .bool _, .bool => true
  | .int _, .int => true
  | .bv w n, .bv w' => w == w' && decide (n < 2 ^ w)
  | _, _ => false

end Val

/-- A default value of each sort. -/
def Ty.default : Ty → Val
  | .bool => .bool false
  | .int => .int 0
  | .bv w => .bv w 0

/-! ## Operators -/

/-- All arguments are Booleans. -/
def bools : List Val → Option (List Bool)
  | [] => some []
  | .bool b :: vs => (bools vs).map (b :: ·)
  | _ :: _ => none

/-- All arguments are integers. -/
def ints : List Val → Option (List Int)
  | [] => some []
  | .int i :: vs => (ints vs).map (i :: ·)
  | _ :: _ => none

/-- Every adjacent pair is related (SMT-LIB `:chainable`). -/
def chain {α : Type} (r : α → α → Bool) : List α → Bool
  | a :: b :: rest => r a b && chain r (b :: rest)
  | _ => true

/-- Pairwise distinct (SMT-LIB `:pairwise`). -/
def pairwiseNe : List Val → Bool
  | [] => true
  | v :: vs => vs.all (· != v) && pairwiseNe vs

/-- Two or more arguments, all of one sort. -/
def sameSort : List Val → Bool
  | v :: w :: rest => (w :: rest).all (·.sort == v.sort)
  | _ => false

/-- The two's complement reading of an `w`-bit vector. -/
def toSigned (w n : Nat) : Int :=
  if n < 2 ^ (w - 1) then n else (n : Int) - 2 ^ w

/-- A binary bit-vector operation on two vectors of one width. -/
def bvBin (f : Nat → Nat → Nat → Nat) : List Val → Option Val
  | [.bv w a, .bv w' b] => if w = w' then some (.bv w (f w a b % 2 ^ w)) else none
  | _ => none

/-- A bit-vector comparison of two vectors of one width. -/
def bvCmp (f : Nat → Nat → Nat → Bool) : List Val → Option Val
  | [.bv w a, .bv w' b] => if w = w' then some (.bool (f w a b)) else none
  | _ => none

/-- A chainable integer comparison. -/
def intCmp (r : Int → Int → Bool) (vs : List Val) : Option Val :=
  if vs.length < 2 then none else (ints vs).map fun is => .bool (chain r is)

/-- The meaning of an operator on argument values; `none` on a sort or arity error. -/
def Op.apply : Op → List Val → Option Val
  | .not, [.bool b] => some (.bool !b)
  | .and, vs => if vs.length < 2 then none else (bools vs).map fun bs => .bool (bs.all id)
  | .or, vs => if vs.length < 2 then none else (bools vs).map fun bs => .bool (bs.any id)
  | .xor, vs => if vs.length < 2 then none else
      (bools vs).map fun bs => .bool (bs.foldl (· ^^ ·) false)
  | .imp, vs => if vs.length < 2 then none else
      (bools vs).map fun bs => .bool (bs.dropLast.foldr (fun a b => !a || b) (bs.getLastD false))
  | .eq, vs => if sameSort vs then some (.bool (chain (· == ·) vs)) else none
  | .distinct, vs => if sameSort vs then some (.bool (pairwiseNe vs)) else none
  | .ite, [.bool c, a, b] => if a.sort == b.sort then some (if c then a else b) else none
  | .add, vs => if vs.length < 2 then none else (ints vs).map fun is => .int (is.foldl (· + ·) 0)
  | .mul, vs => if vs.length < 2 then none else (ints vs).map fun is => .int (is.foldl (· * ·) 1)
  | .sub, [.int i] => some (.int (-i))
  | .sub, .int i :: vs => if vs.isEmpty then none else
      (ints vs).map fun is => .int (is.foldl (· - ·) i)
  | .le, vs => intCmp (fun a b => decide (a ≤ b)) vs
  | .lt, vs => intCmp (fun a b => decide (a < b)) vs
  | .ge, vs => intCmp (fun a b => decide (a ≥ b)) vs
  | .gt, vs => intCmp (fun a b => decide (a > b)) vs
  | .div, [.int a, .int b] => some (.int (a / b))
  | .mod, [.int a, .int b] => some (.int (a % b))
  | .abs, [.int a] => some (.int a.natAbs)
  | .bvadd, vs => bvBin (fun _ a b => a + b) vs
  | .bvsub, vs => bvBin (fun w a b => a + (2 ^ w - b)) vs
  | .bvmul, vs => bvBin (fun _ a b => a * b) vs
  | .bvand, vs => bvBin (fun _ a b => a &&& b) vs
  | .bvor, vs => bvBin (fun _ a b => a ||| b) vs
  | .bvxor, vs => bvBin (fun _ a b => a ^^^ b) vs
  | .bvshl, vs => bvBin (fun w a b => if b < w then a <<< b else 0) vs
  | .bvlshr, vs => bvBin (fun _ a b => a >>> b) vs
  | .bvneg, [.bv w a] => some (.bv w ((2 ^ w - a) % 2 ^ w))
  | .bvnot, [.bv w a] => some (.bv w (2 ^ w - 1 - a))
  | .bvult, vs => bvCmp (fun _ a b => decide (a < b)) vs
  | .bvule, vs => bvCmp (fun _ a b => decide (a ≤ b)) vs
  | .bvugt, vs => bvCmp (fun _ a b => decide (a > b)) vs
  | .bvuge, vs => bvCmp (fun _ a b => decide (a ≥ b)) vs
  | .bvslt, vs => bvCmp (fun w a b => decide (toSigned w a < toSigned w b)) vs
  | .bvsle, vs => bvCmp (fun w a b => decide (toSigned w a ≤ toSigned w b)) vs
  | .bvsgt, vs => bvCmp (fun w a b => decide (toSigned w a > toSigned w b)) vs
  | .bvsge, vs => bvCmp (fun w a b => decide (toSigned w a ≥ toSigned w b)) vs
  | .concat, [.bv w a, .bv w' b] => some (.bv (w + w') (a * 2 ^ w' + b))
  | _, _ => none

/-! ## Evaluation and the denotation -/

mutual
/-- Evaluate a term; `Γ` lists the declared symbols with their sorts. -/
def Term.eval (Γ : List (String × Ty)) (ρ : Model) : Term → Option Val
  | .var x => if Γ.any (·.1 == x) then some (ρ x) else none
  | .bool b => some (.bool b)
  | .int n => some (.int n)
  | .bv w n => if n < 2 ^ w then some (.bv w n) else none
  | .app op args => (Args.eval Γ ρ args).bind op.apply

/-- Evaluate a list of terms. -/
def Args.eval (Γ : List (String × Ty)) (ρ : Model) : Args → Option (List Val)
  | .nil => some []
  | .cons t ts => (Term.eval Γ ρ t).bind fun v => (Args.eval Γ ρ ts).map (v :: ·)
end

namespace Script

/-- The declared symbols, with their sorts. -/
def decls (s : Script) : List (String × Ty) :=
  s.cmds.filterMap fun | .declare x σ => some (x, σ) | _ => none

/-- The assertions. -/
def asserts (s : Script) : List Term :=
  s.cmds.filterMap fun | .assert t => some t | _ => none

/-- The value of `(set-info :status …)`, if any. -/
def status (s : Script) : Option String :=
  s.cmds.findSome? fun | .setInfo ":status" v => some v | _ => none

/-- `ρ` is a model of `s`: every declared symbol has a value of its sort, and every assertion
is `true`. -/
def Holds (s : Script) (ρ : Model) : Prop :=
  (s.decls.all fun d => (ρ d.1).hasSort d.2) = true ∧
  (s.asserts.all fun t => t.eval s.decls ρ == some (.bool true)) = true

instance (s : Script) (ρ : Model) : Decidable (s.Holds ρ) := by
  unfold Holds; infer_instance

/-- The script is satisfiable (the SMT answer `sat`). -/
def Sat (s : Script) : Prop := ∃ ρ, s.Holds ρ

/-- The script's own `:status` is correct (`True` when it states none, or `unknown`). -/
def Expected (s : Script) : Prop :=
  match s.status with
  | some "sat" => s.Sat
  | some "unsat" => ¬ s.Sat
  | _ => True

/-- Every declared symbol at the default value of its sort. -/
def defaultModel (s : Script) : Model :=
  fun x => ((s.decls.lookup x).map Ty.default).getD (.bool false)

/-- Every assertion evaluates to a Boolean under the default model (well sorted). -/
def wellSorted (s : Script) : Bool :=
  s.asserts.all fun t => match t.eval s.decls s.defaultModel with
    | some (.bool _) => true
    | _ => false

/-- Symbols are declared once; at most one `check-sat`, with no declaration or assertion
after it. -/
def wellFormed (s : Script) : Bool :=
  nodup (s.decls.map (·.1)) && go false s.cmds
where
  nodup : List String → Bool
    | [] => true
    | x :: xs => !xs.contains x && nodup xs
  go : Bool → List Cmd → Bool
    | _, [] => true
    | true, .checkSat :: _ | true, .declare .. :: _ | true, .assert _ :: _ => false
    | _, .checkSat :: cs => go true cs
    | seen, _ :: cs => go seen cs

end Script

/-! ## Decoding S-expressions -/

/-- Operator names. -/
def opTable : List (String × Op) :=
  [("not", .not), ("and", .and), ("or", .or), ("=>", .imp), ("xor", .xor), ("=", .eq),
   ("distinct", .distinct), ("ite", .ite), ("+", .add), ("-", .sub), ("*", .mul), ("<=", .le),
   ("<", .lt), (">=", .ge), (">", .gt), ("div", .div), ("mod", .mod), ("abs", .abs),
   ("bvadd", .bvadd), ("bvsub", .bvsub), ("bvmul", .bvmul), ("bvneg", .bvneg),
   ("bvand", .bvand), ("bvor", .bvor), ("bvxor", .bvxor), ("bvnot", .bvnot),
   ("bvshl", .bvshl), ("bvlshr", .bvlshr), ("bvult", .bvult), ("bvule", .bvule),
   ("bvugt", .bvugt), ("bvuge", .bvuge), ("bvslt", .bvslt), ("bvsle", .bvsle),
   ("bvsgt", .bvsgt), ("bvsge", .bvsge), ("concat", .concat)]

def binVal (c : Char) : Option Nat :=
  if c = '0' then some 0 else if c = '1' then some 1 else none

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A symbol of the fragment: a nonempty token not starting with a digit, `#`, `:` or `|`
(quoted symbols are not supported). -/
def isSymbol (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: _ => !(decVal c).isSome && c != '#' && c != ':' && c != '|' && c != '"'

/-- Decode an atom as a term. -/
def decodeAtom (a : String) : Option Term :=
  if a == "true" then some (.bool true)
  else if a == "false" then some (.bool false)
  else match a.toList with
    | '#' :: 'b' :: ds => (digits 2 binVal ds).map (.bv ds.length)
    | '#' :: 'x' :: ds => (digits 16 hexVal ds).map (.bv (4 * ds.length))
    | cs@(c :: _) =>
        if (decVal c).isSome then (digits 10 decVal cs).map .int
        else if isSymbol a then some (.var a) else none
    | [] => none

/-- All `some`. -/
def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | a :: as => a.bind fun a => (allSome as).map (a :: ·)

/-! ## Decoding -/

/-- Decode a sort. -/
def decodeSort : SE → Option Ty
  | .atom "Bool" => some .bool
  | .atom "Int" => some .int
  | .list [.atom "_", .atom "BitVec", .atom w] => (digits 10 decVal w.toList).map .bv
  | _ => none

/-- An indexed bit-vector literal `(_ bvN w)`. -/
def decodeIndexedBv (nm w : String) : Option Term :=
  match nm.toList with
  | 'b' :: 'v' :: ds => do
      let v ← digits 10 decVal ds
      let w ← digits 10 decVal w.toList
      if v < 2 ^ w then some (.bv w v) else none
  | _ => none

mutual
/-- Decode a term. -/
def decodeTerm : SE → Option Term
  | .atom a => decodeAtom a
  | .list [.atom "_", .atom nm, .atom w] => decodeIndexedBv nm w
  | .list (.atom f :: e :: es) => do
      let op ← opTable.lookup f
      let args ← decodeArgs (e :: es)
      some (.app op args)
  | .list _ => none
/-- Decode arguments. -/
def decodeArgs : List SE → Option Args
  | [] => some .nil
  | e :: es => do
      let t ← decodeTerm e
      let ts ← decodeArgs es
      some (.cons t ts)
end

/-- Decode a command. -/
def decodeCmd : SE → Option Cmd
  | .list [.atom "set-logic", .atom l] => some (.setLogic l)
  | .list [.atom "set-info", .atom k, .atom v] => some (.setInfo k v)
  | .list (.atom "set-info" :: .atom k :: _) => some (.setInfo k "")
  | .list [.atom "declare-const", .atom x, σ] =>
      if isSymbol x then (decodeSort σ).map (.declare x) else none
  | .list [.atom "declare-fun", .atom x, .list [], σ] =>
      if isSymbol x then (decodeSort σ).map (.declare x) else none
  | .list [.atom "assert", t] => (decodeTerm t).map .assert
  | .list [.atom "check-sat"] => some .checkSat
  | .list [.atom "exit"] => some .exit
  | .list (.atom c :: _) =>
      if ["set-option", "get-model", "get-info", "get-value", "get-assertions", "echo"].contains c
      then some (.ignored c) else none
  | _ => none

/-- Decode a script from its forms. Rejects ill-formed or ill-sorted scripts. -/
def decodeScript (forms : List SE) : Option Script := do
  let cmds ← allSome (forms.map decodeCmd)
  let s : Script := ⟨cmds⟩
  if s.wellFormed && s.wellSorted then some s else none

/-- Read SMT-LIB v2 bytes in the fragment. -/
def Script.ofBytes? (bytes : List UInt8) : Option Script :=
  readForms bytes >>= decodeScript

/-- Read SMT-LIB v2 text in the fragment. Characters are mapped to bytes one by one (a
non-ASCII character becomes the rejected byte 128), which agrees with `ofBytes?` on the UTF-8
encoding for ASCII text and rejects the rest; it avoids `String.toUTF8`, whose body is not
exposed to the kernel in module files. -/
def Script.parse? (text : String) : Option Script :=
  Script.ofBytes? (text.toList.map fun c => UInt8.ofNat (min c.toNat 128))

end Silmaril.Logic.Smt
