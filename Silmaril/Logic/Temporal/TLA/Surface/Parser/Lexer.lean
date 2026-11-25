module

public import Silmaril.Logic.Temporal.TLA.Surface.Parser.Diagnostic
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Operators
import Std.Data.HashMap

public section

namespace Silmaril.Logic.Temporal.TLA.Surface.Parser

inductive TokenKind where
  | ident | keyword | symbol | number | string | step | beginModule | separator | endModule | eof
  deriving BEq, Inhabited

structure Token where
  kind : TokenKind
  text : String
  span : Span
  deriving Inhabited

private def keywords : List String := [
  "ACTION", "ACTIONS", "ASSUME", "ASSUMPTION", "AXIOM", "CASE", "CHOOSE", "CONSTANT",
  "CONSTANTS", "ELSE", "EXCEPT", "EXTENDS", "IF", "INSTANCE", "LET", "IN", "LOCAL",
  "MODULE", "NEW", "OTHER", "PROPOSITION", "LEMMA", "COROLLARY", "THEN", "BY", "ONLY",
  "DEFINE", "DEF", "DEFS", "THEOREM", "USE", "HIDE", "HAVE", "OBVIOUS", "OMITTED",
  "LAMBDA", "TAKE", "PROOF", "PROVE", "QED", "RECURSIVE", "STATE", "TEMPORAL",
  "TEMPORALS", "PICK", "WITNESS", "SUFFICES", "VARIABLE", "VARIABLES", "WITH",
  "ENABLED", "UNCHANGED", "SUBSET", "UNION", "DOMAIN", "WF_", "SF_"]

private def punctuation : List String := [
  "[]ASSUME", "[]PROVE", "\\E", "\\exists", "∃", "\\A", "\\forall", "∀", "\\EE", "\\AA",
  ",", ":", "::", "∷", "_", "==", "≜", "(", ")", "-|-", "[", "]_", "]", "{", "}",
  "<<", "⟨", ">>_", "⟩_", ">>", "⟩", "!", "->", "→", "<-", "←", "|->", "↦", "@", "--->"]

private def symbolBuckets : Std.HashMap Char (List (List Char × String)) :=
  let spellings := punctuation ++ operatorGroups.flatMap (fun (op, aliases) =>
    op.canonical :: aliases)
  (spellings.mergeSort (fun a b => a.length ≥ b.length)).foldr (fun spelling table =>
    match spelling.toList with
    | [] => table
    | c :: cs => table.insert c ((c :: cs, spelling) :: table.getD c [])) {}

private structure Cursor where
  rest : List Char
  pos : Position := ⟨0, 1, 1⟩
  afterCR : Bool := false

private def Cursor.advance (cursor : Cursor) : Cursor :=
  match cursor.rest with
  | [] => cursor
  | c :: rest =>
    let pos := cursor.pos
    let line := if c == '\r' || (c == '\n' && !cursor.afterCR) then pos.line + 1 else pos.line
    let column :=
      if c == '\r' || c == '\n' then 1
      else if c == '\t' then (pos.column - 1) / 8 * 8 + 9
      else pos.column + 1
    ⟨rest, ⟨pos.byteOffset + c.utf8Size, line, column⟩, c == '\r'⟩

private def Cursor.skip (cursor : Cursor) (count : Nat) : Cursor :=
  match count with
  | 0 => cursor
  | n + 1 => cursor.advance.skip n

private def lexicalError (start stop : Cursor) (message : String) : Diagnostic :=
  ⟨.lexical, ⟨start.pos, stop.pos⟩, message⟩

private partial def skipBlock (start cursor : Cursor) (depth : Nat) : Except Diagnostic Cursor :=
  match cursor.rest with
  | [] => .error (lexicalError start cursor "unterminated block comment")
  | '(' :: '*' :: _ => skipBlock start (cursor.skip 2) (depth + 1)
  | '*' :: ')' :: _ =>
    if depth == 1 then .ok (cursor.skip 2) else skipBlock start (cursor.skip 2) (depth - 1)
  | _ :: _ => skipBlock start cursor.advance depth

private def escapeChar (c : Char) : Option Char :=
  match c with
  | 'n' => some '\n'
  | 't' => some '\t'
  | 'r' => some '\r'
  | 'f' => some (Char.ofNat 12)
  | '\\' => some '\\'
  | '"' => some '"'
  | _ => none

private partial def readString (start cursor : Cursor) (chars : List Char) :
    Except Diagnostic (String × Cursor) :=
  match cursor.rest with
  | '"' :: _ => .ok (String.ofList chars.reverse, cursor.advance)
  | '\\' :: c :: _ =>
    match escapeChar c with
    | some decoded => readString start (cursor.skip 2) (decoded :: chars)
    | none => .error (lexicalError cursor (cursor.skip 2) "invalid string escape")
  | [] | '\r' :: _ | '\n' :: _ =>
    .error (lexicalError start cursor "unterminated string literal")
  | c :: _ => readString start cursor.advance (c :: chars)

private def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

private def wordChar (c : Char) : Bool := asciiLetter c || c.isDigit || c == '_'

private def baseDigits (tag : Char) : Char → Bool :=
  match tag with
  | 'b' | 'B' => fun c => c == '0' || c == '1'
  | 'o' | 'O' => fun c => '0' ≤ c && c ≤ '7'
  | 'h' | 'H' => fun c => c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f')
  | _ => fun _ => false

private def basedNumber (chars : List Char) : List Char :=
  match chars with
  | '\\' :: tag :: rest =>
    match rest.takeWhile (baseDigits tag) with
    | [] => []
    | digits => '\\' :: tag :: digits
  | _ => []

private def proofStep (chars : List Char) : List Char := Id.run do
  let '<' :: tail := chars | return []
  let level := match tail with
    | '*' :: _ => ['*']
    | '+' :: _ => ['+']
    | _ => tail.takeWhile Char.isDigit
  if level.isEmpty then return []
  let '>' :: tail := tail.drop level.length | return []
  let name := tail.takeWhile wordChar
  let suffix := match tail with
    | '*' :: _ | '-' :: _ => tail.take 1 ++ ((tail.drop 1).takeWhile (· == '.'))
    | _ => name ++ ((tail.drop name.length).takeWhile (· == '.'))
  return '<' :: level ++ '>' :: suffix

private def lexeme (c : Char) (chars : List Char) : TokenKind × String × Nat := Id.run do
  if c == '-' || c == '=' then
    let run := chars.takeWhile (· == c)
    if run.length ≥ 4 then
      if c == '=' then return (.endModule, String.ofList run, run.length)
      let spaces := (chars.drop run.length).takeWhile (· == ' ')
      let afterSpaces := chars.drop (run.length + spaces.length)
      if "MODULE".toList.isPrefixOf afterSpaces then
        return (.beginModule, "MODULE", run.length + spaces.length + 6)
      return (.separator, String.ofList run, run.length)
  if ['W', 'F', '_'].isPrefixOf chars then return (.keyword, "WF_", 3)
  if ['S', 'F', '_'].isPrefixOf chars then return (.keyword, "SF_", 3)
  if wordChar c then
    let word := chars.takeWhile wordChar
    if word.any asciiLetter then
      let spelling := String.ofList word
      return (if keywords.contains spelling then .keyword else .ident, spelling, word.length)
    if c.isDigit then
      let digits := word.takeWhile Char.isDigit
      return (.number, String.ofList digits, digits.length)
  if c == 'ℕ' || c == 'ℤ' || c == 'ℝ' || c == '@' then return (.ident, String.singleton c, 1)
  let fixed := (symbolBuckets.getD c []).find? (fun (spelling, _) => spelling.isPrefixOf chars)
  let fixedLength := fixed.map (fun (spelling, _) => spelling.length) |>.getD 0
  let special := if c == '<' then proofStep chars else if c == '\\' then basedNumber chars else []
  if special.length > fixedLength then
    return (if c == '<' then .step else .number, String.ofList special, special.length)
  if let some (_, spelling) := fixed then return (.symbol, spelling, fixedLength)
  return (.symbol, String.singleton c, 0)

private partial def scan (cursor : Cursor) (tokens : Array Token) : Except Diagnostic (Array Token) :=
  match cursor.rest with
  | [] => .ok (tokens.push ⟨.eof, "", ⟨cursor.pos, cursor.pos⟩⟩)
  | '\\' :: '*' :: _ =>
    let comment := (cursor.rest.drop 2).takeWhile (fun c => c != '\n' && c != '\r')
    scan (cursor.skip (2 + comment.length)) tokens
  | '(' :: '*' :: _ => do
    scan (← skipBlock cursor (cursor.skip 2) 1) tokens
  | '"' :: _ => do
    let (decoded, next) ← readString cursor cursor.advance []
    scan next (tokens.push ⟨.string, decoded, ⟨cursor.pos, next.pos⟩⟩)
  | c :: _ =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then scan cursor.advance tokens
    else
      let (kind, spelling, length) := lexeme c cursor.rest
      if length == 0 then
        .error (lexicalError cursor cursor.advance s!"unrecognized character {spelling}")
      else
        let next := cursor.skip length
        scan next (tokens.push ⟨kind, spelling, ⟨cursor.pos, next.pos⟩⟩)

def tokenize (source : String) : Except Diagnostic (Array Token) :=
  scan { rest := source.toList } #[]

end Silmaril.Logic.Temporal.TLA.Surface.Parser
