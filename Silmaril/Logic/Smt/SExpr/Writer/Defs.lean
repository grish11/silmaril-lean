module

public import Silmaril.Logic.Smt.SExpr.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.SExpr.Writer

/-- A non-delimiting byte accepted by the existing ASCII lexer. DEL (127) is
included because the reader accepts it. -/
def LegalChar (c : Char) : Prop :=
  33 ≤ c.toNat ∧ c.toNat < 128 ∧ c.toNat ≠ 34 ∧ c.toNat ≠ 40 ∧
    c.toNat ≠ 41 ∧ c.toNat ≠ 59 ∧ c.toNat ≠ 124

/-- Empty atoms and atoms containing delimiters cannot be emitted faithfully. -/
def LegalAtom (s : String) : Prop :=
  s.toList ≠ [] ∧ ∀ c ∈ s.toList, LegalChar c

/-- Every atom in the actual expression is legal; no parser oracle is assumed. -/
inductive LegalExpr : SE → Prop where
  | atom {s : String} : LegalAtom s → LegalExpr (.atom s)
  | list {es : List SE} : (∀ e ∈ es, LegalExpr e) → LegalExpr (.list es)

/-- Atom bytes are executable without UTF-8 conversion lemmas. Legal atoms are
ASCII, so character values fit in bytes. -/
def atomBytes (s : String) : List UInt8 :=
  s.toList.map (fun c => UInt8.ofNat c.toNat)

/-- A separator follows every token, including parentheses. -/
def tokenBytes : Tok → List UInt8
  | .lp => [40, 32]
  | .rp => [41, 32]
  | .atom s => atomBytes s ++ [32]

def renderTokens (ts : List Tok) : List UInt8 := ts.flatMap tokenBytes

mutual
/-- Emit structural tokens without introducing or changing atoms. -/
def tokens : SE → List Tok
  | .atom s => [.atom s]
  | .list es => .lp :: (tokensForms es ++ [.rp])

def tokensForms : List SE → List Tok
  | [] => []
  | e :: es => tokens e ++ tokensForms es
end

/-- Render any forms; round-trip requires `LegalExpr` for their atoms. -/
def renderForms (es : List SE) : List UInt8 := renderTokens (tokensForms es)

def render (e : SE) : List UInt8 := renderForms [e]

end Silmaril.Logic.Smt.SExpr.Writer
