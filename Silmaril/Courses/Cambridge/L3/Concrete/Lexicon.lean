module

public import Silmaril.Courses.Cambridge.Concrete.LexerProofs

/-! L3 reserves its additional words after the shared UTF-8 lexer.
This keeps the lexical names of the earlier languages available there. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Concrete

open Silmaril.Courses.Cambridge.Concrete

def recognizeDataKeyword : String → Option DataKeyword
  | "fst" => some .fst
  | "snd" => some .snd
  | "inl" => some .inl
  | "inr" => some .inr
  | "match" => some .matchK
  | "with" => some .withK
  | "ref" => some .ref
  | _ => none

def reserve : Token → Token
  | .variable name =>
      match recognizeDataKeyword name with
      | some keyword => .keyword (.data keyword)
      | none => .variable name
  | token => token

def baseSpelling : Token → Token
  | .keyword (.data keyword) => .variable keyword.text
  | token => token

def lex (bytes : ByteArray) : Option (List Token) :=
  (tokenize bytes).map (List.map reserve)

def renderL3 (tokens : List Token) : ByteArray :=
  render (tokens.map baseSpelling)

/-- Variable and field names share the identifier spelling in this profile.
Their source positions distinguish the two syntactic classes. -/
def IsName (name : String) : Prop :=
  IsVariable name ∧ recognizeDataKeyword name = none

instance (name : String) : Decidable (IsName name) := inferInstanceAs (Decidable (_ ∧ _))

/-- The notes enumerate the names as `l, l0, l1, …`. Use that order for
the natural-number location representation of the course AST. -/
def addressChars : Nat → List Char
  | 0 => ['l']
  | n + 1 => 'l' :: n.repr.toList

def addressToken (address : Nat) : Token :=
  .location (String.ofList (addressChars address))

def readAddress (name : String) : Option Nat :=
  match name.toList with
  | ['l'] => some 0
  | 'l' :: digits => do
    let suffix := String.ofList digits
    let n ← suffix.toNat?
    if suffix = n.repr then some (n + 1) else none
  | _ => none

theorem readAddress_addressChars (address : Nat) :
    readAddress (String.ofList (addressChars address)) = some address := by
  cases address with
  | zero => rfl
  | succ n =>
    have h : n.repr.toList ≠ [] := by
      rw [Nat.toList_repr]
      exact Nat.toDigits_ne_nil
    cases hs : n.repr.toList with
    | nil => exact (h hs).elim
    | cons digit digits =>
      have hs' : String.ofList (digit :: digits) = n.repr := by
        rw [← hs, String.ofList_toList]
      simp [readAddress, addressChars, hs, hs']

/-- Tokens whose canonical bytes are read back as the same L3 tokens. -/
def Spellable (token : Token) : Prop :=
  (baseSpelling token).Spellable ∧ reserve (baseSpelling token) = token

@[simp] theorem spell_keyword (keyword : Keyword) : Spellable (.keyword keyword) := by
  cases keyword with
  | data key =>
    cases key <;> (
      refine ⟨?_, rfl⟩
      change IsVariable _
      decide)
  | _ => exact ⟨trivial, rfl⟩

@[simp] theorem spell_punct (punct : Punct) : Spellable (.punct punct) := ⟨trivial, rfl⟩

@[simp] theorem spell_number (n : Nat) : Spellable (.number n) := ⟨trivial, rfl⟩

@[simp] theorem spell_name_iff (name : String) : Spellable (.variable name) ↔ IsName name := by
  cases h : recognizeDataKeyword name <;>
    simp [Spellable, baseSpelling, reserve, Token.Spellable, IsName, h]

private theorem spell_addressChars (digits : List Char) (hd : digits.all Char.isDigit = true) :
    IsLocation (String.ofList ('l' :: digits)) := by
  have hw : digits.all wordChar = true :=
    List.all_eq_true.mpr (fun c hc => by
      simp [wordChar, Char.isAlphanum, List.all_eq_true.mp hd c hc])
  refine ⟨?_, ?_⟩
  · simp [IsWord, String.toList_ofList, List.all_cons, hw]
    decide
  · simp only [String.toList_ofList, classifyWord, List.all_cons]
    change (if false && digits.all Char.isDigit then _ else _) = _
    simp [locationWord, hd]

@[simp] theorem spell_address (address : Nat) : Spellable (addressToken address) := by
  refine ⟨?_, rfl⟩
  change IsLocation (String.ofList (addressChars address))
  cases address with
  | zero => exact spell_addressChars [] rfl
  | succ n =>
    apply spell_addressChars
    rw [Nat.toList_repr]
    exact List.all_eq_true.mpr (fun _ h => Nat.isDigit_of_mem_toDigits (by decide) (by decide) h)

theorem lex_renderL3 (tokens : List Token) (h : ∀ token ∈ tokens, Spellable token) :
    lex (renderL3 tokens) = some tokens := by
  unfold lex renderL3
  rw [tokenize_render]
  · simp only [Option.map_some, List.map_map, Option.some.injEq]
    calc
      tokens.map (reserve ∘ baseSpelling) = tokens.map id :=
        List.map_congr_left (fun _ hm => (h _ hm).2)
      _ = tokens := List.map_id _
  · intro token hm
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hm
    exact (h source hs).1

end Silmaril.Courses.Cambridge.L3.Concrete
