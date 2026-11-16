module

public import Silmaril.Logic.Prolog.Source.Syntax.Defs

/-! A total reader for an explicit pure definite-clause Prolog grammar.
Integers are constructor names, not arithmetic operations. Predicate names with
reserved operational meaning are rejected. Every source character must be consumed. -/
@[expose] public section
namespace Silmaril.Logic.Prolog.Source.Parser

inductive Token where
  | atom : String → Token
  | variable : String → Token
  | integer : Int → Token
  | leftParen | rightParen | leftBracket | rightBracket | bar | comma | dot | rule | query | equal
  deriving DecidableEq, BEq, Repr

def lower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def upper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def identifier (c : Char) : Bool := lower c || upper c || digit c || c == '_'
def decimal (cs : List Char) : Nat :=
  cs.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- Comments may nest. Unterminated block comments are rejected. -/
def blockComment : Nat → Nat → List Char → Option (List Char)
  | 0, _, _ => none
  | _ + 1, 0, cs => some cs
  | fuel + 1, depth + 1, '/' :: '*' :: cs => blockComment fuel (depth + 2) cs
  | fuel + 1, depth + 1, '*' :: '/' :: cs =>
      match depth with
      | 0 => some cs
      | n + 1 => blockComment fuel (n + 1) cs
  | fuel + 1, depth + 1, _ :: cs => blockComment fuel (depth + 1) cs
  | _ + 1, _ + 1, [] => none

/-- Quoted atoms support doubled quotes and the explicit escapes below.
Unknown escapes and unescaped line breaks are rejected. -/
def quoted : Nat → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | fuel + 1, '\'' :: '\'' :: cs, acc => quoted fuel cs ('\'' :: acc)
  | _ + 1, '\'' :: cs, acc => some (String.ofList acc.reverse, cs)
  | fuel + 1, '\\' :: c :: cs, acc => do
      let decoded ← match c with
        | 'n' => some '\n'
        | 'r' => some '\r'
        | 't' => some '\t'
        | '\\' => some '\\'
        | '\'' => some '\''
        | '"' => some '"'
        | _ => none
      quoted fuel cs (decoded :: acc)
  | fuel + 1, c :: cs, acc =>
      if c == '\n' || c == '\r' || c == '\\' then none
      else quoted fuel cs (c :: acc)
  | _ + 1, [], _ => none

/-- A full-stop terminator is followed by layout, a comment, or end of input. -/
def afterFullStop : List Char → Bool
  | [] => true
  | '%' :: _ => true
  | '/' :: '*' :: _ => true
  | c :: _ => c.isWhitespace

/-- Lexing is bounded by the character count and accepts no unknown punctuation. -/
def lex : Nat → List Char → Option (List Token)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, c :: cs => do
      if c.isWhitespace then lex fuel cs
      else if c == '%' then lex fuel (cs.dropWhile (fun x => x != '\n'))
      else match c, cs with
        | '/', '*' :: rest => do
            let rest ← blockComment fuel 1 rest
            lex fuel rest
        | '\'', rest => do
            let (name, rest) ← quoted fuel rest []
            return .atom name :: (← lex fuel rest)
        | ':', '-' :: rest => return .rule :: (← lex fuel rest)
        | '?', '-' :: rest => return .query :: (← lex fuel rest)
        | '=', rest => return .equal :: (← lex fuel rest)
        | '(', rest => return .leftParen :: (← lex fuel rest)
        | ')', rest => return .rightParen :: (← lex fuel rest)
        | '[', rest => return .leftBracket :: (← lex fuel rest)
        | ']', rest => return .rightBracket :: (← lex fuel rest)
        | '|', rest => return .bar :: (← lex fuel rest)
        | ',', rest => return .comma :: (← lex fuel rest)
        | '.', rest =>
            if afterFullStop rest then return .dot :: (← lex fuel rest) else none
        | '-', d :: rest =>
            if digit d then
              let ds := d :: rest.takeWhile digit
              let rest := rest.dropWhile digit
              return .integer (-(Int.ofNat (decimal ds))) :: (← lex fuel rest)
            else none
        | '+', d :: rest =>
            if digit d then
              let ds := d :: rest.takeWhile digit
              let rest := rest.dropWhile digit
              return .integer (Int.ofNat (decimal ds)) :: (← lex fuel rest)
            else none
        | _, _ =>
            if digit c then
              let ds := c :: cs.takeWhile digit
              return .integer (Int.ofNat (decimal ds)) :: (← lex fuel (cs.dropWhile digit))
            else if lower c then
              let name := String.ofList (c :: cs.takeWhile identifier)
              return .atom name :: (← lex fuel (cs.dropWhile identifier))
            else if upper c || c == '_' then
              let name := String.ofList (c :: cs.takeWhile identifier)
              return .variable name :: (← lex fuel (cs.dropWhile identifier))
            else none

/-- Reserved names are rejected as predicate calls and heads, even when quoted.
They remain ordinary data atoms inside terms. This conservative profile does
not reinterpret operational builtins as arbitrary declarative relations. -/
def reservedPredicate (name : String) : Bool :=
  ["true", "fail", "false", "is", "call", "once", "repeat", "not", "!", "\\+",
   "=", "\\=", "==", "\\==", "=@=", "\\=@=", "=..", "<", ">", "=<", ">=", "=:=", "=\\=",
   "var", "nonvar", "atom", "integer", "float", "number", "atomic", "compound", "ground",
   "write", "writeq", "write_canonical", "writeln", "read", "read_term", "nl", "put_char",
   "get_char", "open", "close", "flush_output", "at_end_of_stream", "set_input", "set_output",
   "assert", "asserta", "assertz", "retract", "retractall", "abolish", "clause", "current_predicate",
   "halt", "throw", "catch", "findall", "bagof", "setof", "copy_term", "functor", "arg",
   "unify_with_occurs_check", "compare", "consult", "ensure_loaded", "op", "initialization",
   "current_op", "dynamic", "multifile", "discontiguous", "module", "use_module",
   "length", "append", "member", "sort", "msort", "keysort", "[]", "."].contains name

structure Cursor where
  tokens : List Token
  nextAnonymous : Nat := 0
  deriving Repr

def nilTerm : NamedTerm := NamedTerm.ofArgs (.atom "[]") []
def consTerm (head tail : NamedTerm) : NamedTerm := NamedTerm.ofArgs (.atom ".") [head, tail]

mutual
  /-- Each `_` gets a new identifier, while named variables retain their spelling. -/
  def term : Nat → Cursor → Option (NamedTerm × Cursor)
    | 0, _ => none
    | fuel + 1, s =>
      match s.tokens with
      | .variable name :: rest =>
          if name == "_" then
            some (.var (.anonymous s.nextAnonymous), ⟨rest, s.nextAnonymous + 1⟩)
          else some (.var (.named name), ⟨rest, s.nextAnonymous⟩)
      | .integer value :: rest =>
          some (NamedTerm.ofArgs (.integer value) [], ⟨rest, s.nextAnonymous⟩)
      | .atom name :: .leftParen :: rest => do
          let (args, s) ← arguments fuel ⟨rest, s.nextAnonymous⟩
          return (NamedTerm.ofArgs (.atom name) args, s)
      | .atom name :: rest =>
          some (NamedTerm.ofArgs (.atom name) [], ⟨rest, s.nextAnonymous⟩)
      | .leftBracket :: .rightBracket :: rest => some (nilTerm, ⟨rest, s.nextAnonymous⟩)
      | .leftBracket :: rest => listTerms fuel ⟨rest, s.nextAnonymous⟩
      | _ => none

  /-- A parenthesized argument sequence is nonempty and consumes its closing `)`. -/
  def arguments : Nat → Cursor → Option (List NamedTerm × Cursor)
    | 0, _ => none
    | fuel + 1, s => do
      let (head, s) ← term fuel s
      match s.tokens with
      | .rightParen :: rest => return ([head], ⟨rest, s.nextAnonymous⟩)
      | .comma :: rest => do
          let (tail, s) ← arguments fuel ⟨rest, s.nextAnonymous⟩
          return (head :: tail, s)
      | _ => none

  /-- Proper and improper list syntax desugars to the explicit `[]`/0 and `.`/2 symbols. -/
  def listTerms : Nat → Cursor → Option (NamedTerm × Cursor)
    | 0, _ => none
    | fuel + 1, s => do
      let (head, s) ← term fuel s
      match s.tokens with
      | .rightBracket :: rest => return (consTerm head nilTerm, ⟨rest, s.nextAnonymous⟩)
      | .comma :: rest => do
          let (tail, s) ← listTerms fuel ⟨rest, s.nextAnonymous⟩
          return (consTerm head tail, s)
      | .bar :: rest => do
          let (tail, s) ← term fuel ⟨rest, s.nextAnonymous⟩
          match s.tokens with
          | .rightBracket :: rest => return (consTerm head tail, ⟨rest, s.nextAnonymous⟩)
          | _ => none
      | _ => none
end

/-- A call is headed by an admitted atom, never an integer, variable or list. -/
def atom (fuel : Nat) (s : Cursor) : Option (NamedAtom × Cursor) := do
  match s.tokens with
  | .atom name :: .leftParen :: rest =>
      if reservedPredicate name then none else do
        let (args, s) ← arguments fuel ⟨rest, s.nextAnonymous⟩
        return (NamedAtom.ofArgs name args, s)
  | .atom name :: rest =>
      if reservedPredicate name then none
      else some (NamedAtom.ofArgs name [], ⟨rest, s.nextAnonymous⟩)
  | _ => none

/-- At least one goal is required; the following sentence terminator is not consumed. -/
def goals : Nat → Cursor → Option (List NamedAtom × Cursor)
  | 0, _ => none
  | fuel + 1, s => do
      let (head, s) ← atom fuel s
      match s.tokens with
      | .comma :: rest => do
          let (tail, s) ← goals fuel ⟨rest, s.nextAnonymous⟩
          return (head :: tail, s)
      | _ => return ([head], s)

def sentence : Nat → Cursor → Option (NamedSentence × Cursor)
  | 0, _ => none
  | fuel + 1, s =>
      match s.tokens with
      | .query :: rest => do
          let (body, s) ← goals fuel ⟨rest, s.nextAnonymous⟩
          match s.tokens with
          | .dot :: rest => return (.query body, ⟨rest, s.nextAnonymous⟩)
          | _ => none
      | _ => do
          let (head, s) ← atom fuel s
          match s.tokens with
          | .dot :: rest => return (.clause head [], ⟨rest, s.nextAnonymous⟩)
          | .rule :: rest => do
              let (body, s) ← goals fuel ⟨rest, s.nextAnonymous⟩
              match s.tokens with
              | .dot :: rest => return (.clause head body, ⟨rest, s.nextAnonymous⟩)
              | _ => none
          | _ => none

/-- Variable scope and anonymous numbering restart at every sentence boundary. -/
def program : Nat → List Token → Option (List NamedSentence)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, tokens => do
      let (first, s) ← sentence fuel ⟨tokens, 0⟩
      match first with
      | .query _ =>
          if s.tokens.isEmpty then some [first] else none
      | .clause _ _ => do
          let rest ← program fuel s.tokens
          return first :: rest

/-- Whole-input single-sentence reader for a clause or query. No trailing
sentence or token is admitted. A query is syntactically distinguished from a
clause; this reader does not assert its goals as program facts. -/
def parseSentence? (text : String) : Option NamedSentence := do
  let chars := text.toList
  let tokens ← lex (chars.length + 1) chars
  let (result, rest) ← sentence (2 * tokens.length + 2) ⟨tokens, 0⟩
  if rest.tokens.isEmpty then some result else none

/-- Whole-input program reader: clauses followed by at most one final query.
A final unterminated sentence or any unsupported suffix rejects the entire text.
Empty/comment-only programs are allowed; empty queries and empty explicit rule
bodies are not part of the grammar. The optional query is kept separate by its
constructor; interpreting a program's clauses is distinct from asking its goal. -/
def parseProgram? (text : String) : Option (List NamedSentence) := do
  let chars := text.toList
  let tokens ← lex (chars.length + 1) chars
  program (2 * tokens.length + 2) tokens

/-- Compatibility name for the whole-program reader used by the controls. -/
def parse (text : String) : Option (List NamedSentence) := parseProgram? text

end Silmaril.Logic.Prolog.Source.Parser
