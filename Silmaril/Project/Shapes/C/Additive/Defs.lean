module

public import Silmaril.Cerberus.Ctype.Defs

/-!
# A restricted C typing judgment: the operands of `+` (C11 §6.5.6¶2)

`AdditiveOperands t₁ t₂`: the constraint of C11 §6.5.6¶2 on the operand types of binary `+`,
"either both operands shall have arithmetic type, or one operand shall be a pointer to a complete
object type and the other shall have integer type", over Cerberus's `Ctype` (after lvalue
conversion; qualifiers and annotations ignored).

This is the **only** typing judgment the explorer states: it is not a typing judgment for C
programs. Completeness of object types is approximated by excluding `void`, function types and
incomplete arrays (struct and union completeness, which needs the tag environment, is not
modelled: a pointer to a struct counts as a pointer to a complete object). `AdditionFragment`
independently recognizes a tiny source grammar in which the two types come from parameters.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.C

open Silmaril.Cerberus

/-- An integer type (`_Bool`, `char`, signed and unsigned integers, enumerations). -/
def IsIntegerType : Ctype → Prop
  | .mk _ (.basic (.integer _)) => True
  | _ => False

/-- An arithmetic type: integer or real floating. -/
def IsArithmeticType : Ctype → Prop
  | .mk _ (.basic _) => True
  | _ => False

/-- A pointer to a complete object type (approximated: not `void`, not a function, not an
array of unknown size). -/
def IsObjectPointerType : Ctype → Prop
  | .mk _ (.pointer _ (.mk _ .void)) => False
  | .mk _ (.pointer _ (.mk _ (.function ..))) => False
  | .mk _ (.pointer _ (.mk _ (.functionNoParams _))) => False
  | .mk _ (.pointer _ (.mk _ (.array _ none))) => False
  | .mk _ (.pointer _ _) => True
  | _ => False

/-- **C11 §6.5.6¶2, for `+`.** -/
inductive AdditiveOperands : Ctype → Ctype → Prop where
  | arith {t₁ t₂ : Ctype} : IsArithmeticType t₁ → IsArithmeticType t₂ → AdditiveOperands t₁ t₂
  | ptrInt {t₁ t₂ : Ctype} : IsObjectPointerType t₁ → IsIntegerType t₂ → AdditiveOperands t₁ t₂
  | intPtr {t₁ t₂ : Ctype} : IsIntegerType t₁ → IsObjectPointerType t₂ → AdditiveOperands t₁ t₂

/-- `int`. -/
def intCtype : Ctype := .mk [] (.basic (.integer (.signed .int)))

/-- `int *`. -/
def intPtrCtype : Ctype := .mk [] (.pointer ⟨false, false, false⟩ intCtype)

namespace AdditionFragment

/-- Split the punctuation and whitespace of the restricted grammar. -/
def tokens (pending : List Char) : List Char → List (List Char)
  | [] => if pending.isEmpty then [] else [pending.reverse]
  | ch :: rest =>
    let flush tail := if pending.isEmpty then tail else pending.reverse :: tail
    if ch.isWhitespace then flush (tokens [] rest)
    else if ['*', '+', '(', ')', '{', '}', ',', ';'].contains ch then flush ([ch] :: tokens [] rest)
    else tokens (ch :: pending) rest

/-- Read an `int` or `int *` parameter with the indicated name. -/
def parameter (name : Char) : List (List Char) → Option (Ctype × List (List Char))
  | ['i', 'n', 't'] :: ['*'] :: [ident] :: rest => if ident == name then some (intPtrCtype, rest) else none
  | ['i', 'n', 't'] :: [ident] :: rest => if ident == name then some (intCtype, rest) else none
  | _ => none

/-- Recognize `int *addp(…, …) { return p + q; }` with `int` or `int *` parameters named
`p` and `q` and either operand order. No preprocessing, comments or other declarators.
Success supplies the declared types in operand order; this does not check the return type. -/
def operands (text : String) : Option (Ctype × Ctype) :=
  do
    let ['i', 'n', 't'] :: ['*'] :: ['a', 'd', 'd', 'p'] :: ['('] :: rest := tokens [] text.toList | none
    let (pType, [','] :: rest) ← parameter 'p' rest | none
    let (qType, [[')'], ['{'], ['r', 'e', 't', 'u', 'r', 'n'], [lhs], ['+'], [rhs], [';'], ['}']]) ←
      parameter 'q' rest | none
    if lhs == 'p' && rhs == 'q' then some (pType, qType)
    else if lhs == 'q' && rhs == 'p' then some (qType, pType)
    else none

/-- A recognized expression, whose input types must satisfy C's additive constraint. -/
def Accepts (text : String) : Prop :=
  ∃ pair, operands text = some pair ∧ AdditiveOperands pair.1 pair.2

end AdditionFragment

end Silmaril.Project.Shapes.C

end
