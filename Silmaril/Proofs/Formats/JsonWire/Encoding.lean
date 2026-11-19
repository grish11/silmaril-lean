module

public import Silmaril.Formats.JsonWire.Defs
public import Silmaril.Formats.JsonWire.Grammar.Thms
import Silmaril.Proofs.Formats.JsonWire.Lexer
import all Init.Data.Int.Repr

@[expose] public section

namespace Silmaril.Proofs.Formats.JsonWire.Encoding

open Silmaril.Formats.JsonWire Silmaril.Formats.JsonWire.Internal
open Silmaril.Formats (JsonIx RawSyn)
open Silmaril.Proofs.Formats.JsonWire.Lexer

private def hexDigit (digit : Nat) : Char := Char.ofNat (if digit < 10 then 48 + digit else 87 + digit)

private theorem hex_hexDigit (digit : Nat) (bound : digit < 16) : hex? (hexDigit digit) = some digit := by
  have casesDigit : digit = 0 ∨ digit = 1 ∨ digit = 2 ∨ digit = 3 ∨ digit = 4 ∨ digit = 5 ∨
      digit = 6 ∨ digit = 7 ∨ digit = 8 ∨ digit = 9 ∨ digit = 10 ∨ digit = 11 ∨ digit = 12 ∨
      digit = 13 ∨ digit = 14 ∨ digit = 15 := by omega
  rcases casesDigit with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def escapeUnit (unit : UInt16) : List Char :=
  '\\' :: 'u' :: (List.range 4).map (fun index => hexDigit (unit.toNat / 16 ^ (3 - index) % 16))

private theorem escapeUnit_read (unit : UInt16) (rest : List Char) :
    escape? .rfc8259 ((escapeUnit unit).drop 1 ++ rest) = some ([unit], rest) := by
  change escape? .rfc8259 ('u' :: hexDigit (unit.toNat / 4096 % 16) ::
    hexDigit (unit.toNat / 256 % 16) :: hexDigit (unit.toNat / 16 % 16) ::
    hexDigit (unit.toNat / 1 % 16) :: rest) = _
  have rebuild : unit.toNat / 4096 % 16 * 4096 +
      (unit.toNat / 256 % 16 * 256 + (unit.toNat / 16 % 16 * 16 + (unit.toNat % 16 + 0))) =
      unit.toNat := by have bound := unit.toNat_lt; omega
  simp only [escape?, hexes?, Nat.div_one, hex_hexDigit _ (Nat.mod_lt _ (by decide : 0 < 16)),
    Bind.bind, Option.bind, Pure.pure, Nat.reducePow, Nat.mul_one]
  rw [rebuild, UInt16.ofNat_toNat]

private theorem quoted_units (units : Units) (rest : List Char) (fuel : Nat) (enough : units.length < fuel) :
    quoted? .rfc8259 '"' fuel (units.flatMap escapeUnit ++ '"' :: rest) = some (units, rest) := by
  induction units generalizing fuel with
  | nil => cases fuel with
    | zero => simp at enough
    | succ => rfl
  | cons unit units ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have readHead := escapeUnit_read unit (units.flatMap escapeUnit ++ '"' :: rest)
      have readTail := ih fuel (by simp only [List.length_cons] at enough; omega)
      rw [List.flatMap_cons, List.append_assoc]
      change quoted? .rfc8259 '"' (fuel + 1)
        ('\\' :: ((escapeUnit unit).drop 1 ++ (units.flatMap escapeUnit ++ '"' :: rest))) = _
      simp [quoted?, -List.drop_one, readHead, readTail]

theorem tokensOf_quote (units : Units) (rest : List Char) :
    tokensOf ((quote units).toList ++ rest) = (tokensOf rest).map (.string units :: ·) := by
  have size : (units.flatMap escapeUnit).length = 6 * units.length := by
    induction units with
    | nil => rfl
    | cons unit units ih => simp [escapeUnit, ih, Nat.mul_succ]; omega
  change tokensOf ((String.ofList ('"' :: (units.flatMap escapeUnit ++ ['"']))).toList ++ rest) = _
  simp only [String.toList_ofList, List.cons_append, List.append_assoc, List.nil_append]
  apply tokensOf_step (k := .string) (t := some (.string units))
  · have enough : units.length < ('"' :: (units.flatMap escapeUnit ++ '"' :: rest)).length + 1 := by
      simp only [List.length_cons, List.length_append, size]
      omega
    have reading := quoted_units units rest _ enough
    have noWhite : white .rfc8259 '"' = false := by decide
    have rfcSame : ((Dialect.rfc8259 : Dialect) != .rfc8259) = false := by decide
    simp only [step, noWhite, rfcSame, Char.reduceBEq, beq_self_eq_true, Bool.false_and,
      Bool.true_or, Bool.false_eq_true, ite_false, ite_true, reading]
    rfl
  · simp only [List.length_append, List.length_cons]
    omega

private theorem repr_digits (value : Nat) : (value.repr.toList).all Char.isDigit = true := by
  simp only [Nat.repr_eq_ofList_toDigits, String.toList_ofList]
  induction value using Nat.base_induction 10 (by decide) with
  | single amount small => simp [Nat.toDigits_of_lt_base small, small]
  | digit amount last small positive ih =>
    rw [← Nat.toDigits_append_toDigits (by decide) positive small]
    simp [ih, Nat.toDigits_of_lt_base small, small]

private theorem repr_nonempty (value : Nat) : value.repr.toList ≠ [] := by
  simp [Nat.repr_eq_ofList_toDigits]

private theorem repr_noLeadingZero (value : Nat) :
    (1 < value.repr.toList.length ∧ value.repr.toList.head? = some '0') → False := by
  simp only [Nat.repr_eq_ofList_toDigits, String.toList_ofList]
  induction value using Nat.base_induction 10 (by decide) with
  | single amount small => simp [Nat.toDigits_of_lt_base small]
  | digit amount last small positive ih =>
    rw [← Nat.toDigits_append_toDigits (by decide) positive small,
      List.head?_append_of_ne_nil _ Nat.toDigits_ne_nil]
    intro ⟨_, zero⟩
    by_cases short : amount < 10
    · simp [Nat.toDigits_of_lt_base short] at zero
      omega
    · have long : 1 < (Nat.toDigits 10 amount).length := by
        rw [Nat.toDigits_of_base_le (by decide) (by omega)]
        simp only [List.length_append, List.length_singleton]
        have := Nat.length_toDigits_pos (b := 10) (n := amount / 10)
        omega
      exact ih ⟨long, zero⟩

private theorem read_digits (digits : List Char) (allDigits : digits.all Char.isDigit = true) (acc : Nat) :
    digits.foldl (fun n c => 10 * n + (hex? c).getD 0) acc = Nat.ofDigitChars 10 digits acc := by
  induction digits generalizing acc with
  | nil => simp
  | cons digit rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at allDigits
    rw [Nat.ofDigitChars_cons, List.foldl_cons, ih allDigits.2]
    simp [hex?, allDigits.1]

private theorem digitsValue_repr (value : Nat) : digitsValue 10 value.repr.toList = value := by
  unfold digitsValue
  rw [read_digits _ (repr_digits value), Nat.repr_eq_ofList_toDigits, String.toList_ofList,
    Nat.ofDigitChars_ten_toDigits]

private theorem repr_head (value : Nat) : ∃ head tail, value.repr.toList = head :: tail ∧ head.isDigit = true := by
  cases parts : value.repr.toList with
  | nil => exact False.elim (repr_nonempty value parts)
  | cons head tail => exact ⟨head, tail, rfl, by simpa [parts] using (List.all_eq_true.mp (repr_digits value) head (by simp [parts]))⟩

private theorem exponent_literal (exponent : Int) :
    exponent? (if exponent = 0 then [] else 'e' :: exponent.repr.toList) = some exponent := by
  cases exponent with
  | ofNat amount =>
    by_cases zero : amount = 0
    · subst amount; rfl
    · obtain ⟨head, tail, parts, digit⟩ := repr_head amount
      have sign : splitSign amount.repr.toList = (false, amount.repr.toList) := by
        apply splitSign_of
        rw [parts]
        rintro char same
        have : head = char := Option.mem_some_iff.mp same
        subst char
        constructor <;> rintro rfl <;> contradiction
      simp [Int.repr, zero, exponent?, sign, List.isEmpty_iff, repr_digits,
        digitsValue_repr, -Nat.toList_repr]
  | negSucc amount =>
    simp [Int.repr, exponent?, splitSign, List.isEmpty_iff, repr_digits,
      digitsValue_repr, -Nat.toList_repr]
    omega

theorem decimal_literal (value : Decimal) : decimal? .rfc8259 value.literal.toList = some (.finite value) := by
  obtain ⟨negative, coefficient, exponent⟩ := value
  let ending := if exponent = 0 then [] else 'e' :: exponent.repr.toList
  have endHead : ∀ char ∈ ending.head?, char = 'e' := by
    by_cases zero : exponent = 0 <;> simp [ending, zero]
  have span : (coefficient.repr.toList ++ ending).span Char.isDigit = (coefficient.repr.toList, ending) :=
    span_append_stop (List.all_eq_true.mp (repr_digits coefficient)) (fun char h => by rw [endHead char h]; decide)
  rw [span_eq] at span
  have take := (Prod.mk.inj span).1
  have drop := (Prod.mk.inj span).2
  have fraction : splitFraction ending = ([], ending, false) :=
    splitFraction_of (fun char h => by rw [endHead char h]; decide)
  have expRead := exponent_literal exponent
  change exponent? ending = some exponent at expRead
  obtain ⟨head, tail, parts, digit⟩ := repr_head coefficient
  have headSign : head ≠ '-' ∧ head ≠ '+' := by constructor <;> rintro rfl <;> contradiction
  have sign : splitSign (coefficient.repr.toList ++ ending) = (false, coefficient.repr.toList ++ ending) := by
    apply splitSign_of
    simp [parts, headSign]
  have noPlus : (coefficient.repr.toList ++ ending).head? ≠ some '+' := by simp [parts, headSign.2]
  have leading : ¬ (1 < coefficient.repr.toList.length ∧ coefficient.repr.toList.head? = some '0') :=
    repr_noLeadingZero coefficient
  have chars : ((if exponent = 0 then "" else "e" ++ exponent.repr)).toList = ending := by
    by_cases zero : exponent = 0 <;> simp [ending, zero]
  simp only [Decimal.literal, String.toList_append, chars]
  cases negative
  · simp [decimal?, sign, take, drop, fraction, expRead, digitsValue_repr, leading, List.isEmpty_iff,
      noPlus, -Nat.toList_repr, -List.head?_append]
  · simp [decimal?, splitSign, take, drop, fraction, expRead, digitsValue_repr, leading, List.isEmpty_iff,
      -Nat.toList_repr]

theorem tokensOf_decimal_literal (value : Decimal) (rest : List Char)
    (follow : ∀ char ∈ rest.head?, delimiter .rfc8259 char = true) :
    tokensOf (value.literal.toList ++ rest) = (tokensOf rest).map (.number (.finite value) :: ·) :=
  Silmaril.Formats.JsonWire.Internal.tokensOf_number_exact (decimal_literal value) follow

private theorem openArray (rest : List Char) :
    tokensOf ('[' :: rest) = (tokensOf rest).map (.arrayOpen :: ·) :=
  tokensOf_punct (.inl ⟨rfl, rfl⟩) rest

private theorem closeArray (rest : List Char) :
    tokensOf (']' :: rest) = (tokensOf rest).map (.arrayClose :: ·) :=
  tokensOf_punct (.inr (.inl ⟨rfl, rfl⟩)) rest

private theorem openObject (rest : List Char) :
    tokensOf ('{' :: rest) = (tokensOf rest).map (.objectOpen :: ·) :=
  tokensOf_punct (.inr (.inr (.inl ⟨rfl, rfl⟩))) rest

private theorem closeObject (rest : List Char) :
    tokensOf ('}' :: rest) = (tokensOf rest).map (.objectClose :: ·) :=
  tokensOf_punct (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))) rest

private theorem comma (rest : List Char) :
    tokensOf (',' :: rest) = (tokensOf rest).map (.comma :: ·) :=
  tokensOf_punct (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))) rest

private theorem colon (rest : List Char) :
    tokensOf (':' :: rest) = (tokensOf rest).map (.colon :: ·) :=
  tokensOf_punct (.inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))) rest

private theorem followsCons (char : Char) (rest : List Char) (delimits : delimiter .rfc8259 char = true) :
    ∀ head ∈ (char :: rest).head?, delimiter .rfc8259 head = true := by
  intro head member
  obtain rfl : char = head := Option.mem_some_iff.mp member
  exact delimits

private theorem tokens_render {index : JsonIx} (tree : Syn Decimal index) (rest : List Char)
    (follow : ∀ char ∈ rest.head?, delimiter .rfc8259 char = true) :
    tokensOf ((render Decimal.literal tree).toList ++ rest) = (tokensOf rest).map (printedTokens tree ++ ·) := by
  induction tree generalizing rest with
  | scalar atom =>
    cases atom with
    | none => exact tokensOf_literal (.inr (.inr ⟨rfl, rfl⟩)) follow
    | some atom =>
      cases atom with
      | bool flag =>
        cases flag
        · exact tokensOf_literal (.inr (.inl ⟨rfl, rfl⟩)) follow
        · exact tokensOf_literal (.inl ⟨rfl, rfl⟩) follow
      | string units => exact tokensOf_quote units rest
      | number number => exact tokensOf_decimal_literal number rest follow
  | list items ih =>
    have close := followsCons ']' rest (by decide)
    simp [render, printedTokens, List.append_assoc, openArray, ih _ close, closeArray, Option.map_map,
      Function.comp_def]
  | map fields ih =>
    have close := followsCons '}' rest (by decide)
    simp [render, printedTokens, List.append_assoc, openObject, ih _ close, closeObject, Option.map_map,
      Function.comp_def]
  | nil | objNil => simp [render, printedTokens]
  | cons value tail ih tailIH =>
    cases tail with
    | nil => simpa [render, printedTokens] using ih rest follow
    | cons next remaining =>
      let tail := RawSyn.cons next remaining
      have follows := followsCons ',' ((render Decimal.literal tail).toList ++ rest) (by decide)
      rw [render, printedTokens] <;> try (intro impossible; cases impossible)
      simp only [String.toList_append, List.append_assoc]
      change tokensOf ((render Decimal.literal value).toList ++ ',' :: ((render Decimal.literal tail).toList ++ rest)) =
        (tokensOf rest).map (fun tokens => printedTokens value ++ .comma :: (printedTokens tail ++ tokens))
      rw [ih _ follows, comma, tailIH _ follow]
      simp [Option.map_map, Function.comp_def, tail]
  | objCons key value tail ih tailIH =>
    cases tail with
    | objNil =>
      simp [render, printedTokens, List.append_assoc, tokensOf_quote, colon, ih _ follow, Option.map_map,
        Function.comp_def]
    | objCons next item remaining =>
      let tail := RawSyn.objCons next item remaining
      have follows := followsCons ',' ((render Decimal.literal tail).toList ++ rest) (by decide)
      rw [render, printedTokens] <;> try (intro impossible; cases impossible)
      simp only [String.toList_append, List.append_assoc, List.cons_append]
      change tokensOf ((quote key).toList ++ ':' :: ((render Decimal.literal value).toList ++
        ',' :: ((render Decimal.literal tail).toList ++ rest))) =
        (tokensOf rest).map (fun tokens => .string key :: .colon ::
          (printedTokens value ++ .comma :: (printedTokens tail ++ tokens)))
      rw [tokensOf_quote, colon, ih _ follows, comma, tailIH _ follow]
      simp [Option.map_map, Function.comp_def, tail]

private theorem mapNumbers_finite {index : JsonIx} (tree : Syn Decimal index) :
    mapNumbers? (fun | .finite number => some number | _ => none) (tree.mapScalar addFinite) = some tree := by
  induction tree with
  | scalar atom => cases atom with
    | none => rfl
    | some atom => cases atom <;> rfl
  | list _ ih | map _ ih => simp [RawSyn.mapScalar, mapNumbers?, ih]
  | nil | objNil => rfl
  | cons _ _ ih tail | objCons _ _ _ ih tail => simp [RawSyn.mapScalar, mapNumbers?, ih, tail]

private def arrayContinue (fuel : Nat) (value : Ast Number) :
    List Token → Option (Syn Number .arr × List Token)
  | .arrayClose :: rest => some (.cons value .nil, rest)
  | .comma :: rest => do
    let (tail, rest) ← array? .rfc8259 fuel false rest
    pure (.cons value tail, rest)
  | _ => none

private theorem array_notClose {fuel : Nat} {tokens : List Token} {value : Ast Number} {rest : List Token}
    (readHead : value? .rfc8259 fuel tokens = some (value, rest)) (allowEmpty : Bool) :
    array? .rfc8259 (fuel + 1) allowEmpty tokens = arrayContinue fuel value rest := by
  simp only [array?]
  split
  · cases fuel <;> simp_all [value?]
  · rw [readHead]
    cases rest with
    | nil => rfl
    | cons token _ => cases token <;> rfl

private def PrintedRead (fuel : Nat) (rest : List Token) : {index : JsonIx} → Syn Decimal index → Prop
  | .val, tree => value? .rfc8259 fuel (printedTokens tree ++ rest) = some (tree.mapScalar addFinite, rest)
  | .arr, tree => ∀ allowEmpty, (tree = .nil → allowEmpty = true) →
      array? .rfc8259 fuel allowEmpty (printedTokens tree ++ .arrayClose :: rest) =
        some (tree.mapScalar addFinite, rest)
  | .obj, tree => ∀ allowEmpty, (tree = .objNil → allowEmpty = true) →
      object? .rfc8259 fuel allowEmpty (printedTokens tree ++ .objectClose :: rest) =
        some (tree.mapScalar addFinite, rest)

private def closingCost : JsonIx → Nat
  | .val => 0
  | .arr | .obj => 1

private theorem read_printed {index : JsonIx} (tree : Syn Decimal index) :
    ∀ fuel : Nat, (printedTokens tree).length + closingCost index < fuel →
      ∀ rest : List Token, PrintedRead fuel rest tree := by
  induction tree with
  | scalar atom =>
    intro fuel enough rest
    cases fuel with
    | zero => omega
    | succ => cases atom with
      | none => rfl
      | some atom => cases atom <;> rfl
  | list items ih =>
    intro fuel enough rest
    cases fuel with
    | zero => omega
    | succ fuel =>
      have readItems := ih fuel (by simp [printedTokens, closingCost] at enough ⊢; omega) rest true (fun _ => rfl)
      simp only [PrintedRead, printedTokens, List.cons_append, List.append_assoc, List.nil_append, RawSyn.mapScalar, value?]
      rw [readItems]
      rfl
  | map fields ih =>
    intro fuel enough rest
    cases fuel with
    | zero => omega
    | succ fuel =>
      have readFields := ih fuel (by simp [printedTokens, closingCost] at enough ⊢; omega) rest true (fun _ => rfl)
      simp only [PrintedRead, printedTokens, List.cons_append, List.append_assoc, List.nil_append, RawSyn.mapScalar, value?]
      rw [readFields]
      rfl
  | nil | objNil =>
    intro fuel enough rest allowEmpty allowed
    have := allowed rfl
    subst allowEmpty
    cases fuel with
    | zero => omega
    | succ => rfl
  | cons value tail ih tailIH =>
    intro fuel enough rest allowEmpty _
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases tail with
      | nil =>
        have readHead := ih fuel (by simp [printedTokens, closingCost] at enough ⊢; omega) (.arrayClose :: rest)
        simpa only [printedTokens, List.append_nil, RawSyn.mapScalar, arrayContinue] using array_notClose readHead allowEmpty
      | cons next remaining =>
        let tail := RawSyn.cons next remaining
        have lengthEq : printedTokens (RawSyn.cons value tail) = printedTokens value ++ .comma :: printedTokens tail := by
          change printedTokens value ++ [Token.comma] ++ printedTokens tail = _
          simp only [List.append_assoc, List.singleton_append]
        rw [lengthEq] at enough
        simp only [List.length_append, List.length_cons, closingCost] at enough
        have readHead := ih fuel (by simp only [closingCost, Nat.add_zero]; omega) (.comma :: (printedTokens tail ++ .arrayClose :: rest))
        have readTail := tailIH fuel (by change (printedTokens tail).length + 1 < fuel; omega) rest false (by intro impossible; cases impossible)
        change array? .rfc8259 (fuel + 1) allowEmpty (printedTokens (.cons value tail) ++ .arrayClose :: rest) = _
        rw [lengthEq, List.append_assoc, List.cons_append, array_notClose readHead allowEmpty]
        change (do let (tailValue, left) ← array? .rfc8259 fuel false (printedTokens tail ++ Token.arrayClose :: rest)
                   pure (RawSyn.cons (value.mapScalar addFinite) tailValue, left)) = _
        rw [readTail]
        rfl
  | objCons key value tail ih tailIH =>
    intro fuel enough rest allowEmpty _
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases tail with
      | objNil =>
        have readHead := ih fuel (by simp [printedTokens, closingCost] at enough ⊢; omega) (.objectClose :: rest)
        simp only [printedTokens, List.append_nil, List.cons_append, RawSyn.mapScalar, object?, Bind.bind, Option.bind]
        rw [readHead]
      | objCons next item remaining =>
        let tail := RawSyn.objCons next item remaining
        have lengthEq : printedTokens (RawSyn.objCons key value tail) =
          .string key :: .colon :: (printedTokens value ++ .comma :: printedTokens tail) := by
          change Token.string key :: Token.colon :: (printedTokens value ++ [Token.comma] ++ printedTokens tail) = _
          simp only [List.append_assoc, List.singleton_append]
        rw [lengthEq] at enough
        simp only [List.length_append, List.length_cons, closingCost] at enough
        have readHead := ih fuel (by simp only [closingCost, Nat.add_zero]; omega) (.comma :: (printedTokens tail ++ .objectClose :: rest))
        have readTail := tailIH fuel (by change (printedTokens tail).length + 1 < fuel; omega) rest false (by intro impossible; cases impossible)
        change object? .rfc8259 (fuel + 1) allowEmpty (printedTokens (.objCons key value tail) ++ .objectClose :: rest) = _
        rw [lengthEq]
        simp only [List.cons_append, List.append_assoc, object?, Bind.bind, Option.bind]
        rw [readHead]
        change (do let (tailValue, left) ← object? .rfc8259 fuel false (printedTokens tail ++ Token.objectClose :: rest)
                   pure (RawSyn.objCons key (value.mapScalar addFinite) tailValue, left)) = _
        rw [readTail]
        rfl

theorem value?_printedTokens (tree : Ast Decimal) (fuel : Nat)
    (enough : (printedTokens tree).length < fuel) (rest : List Token) :
    value? .rfc8259 fuel (printedTokens tree ++ rest) = some (tree.mapScalar addFinite, rest) :=
  read_printed tree fuel (by simpa [closingCost] using enough) rest

theorem parse_encode (tree : Ast Decimal) : parse? (encode tree) = some tree := by
  let text := render Decimal.literal tree
  have fromResult : String.fromUTF8? text.toByteArray = some text := by
    unfold String.fromUTF8?
    rw [dite_eq_left text.isValidUTF8, Option.some.injEq]
    exact String.toByteArray_inj.mp rfl
  have tokenized : tokensOf text.toList = some (printedTokens tree) := by
    simpa using tokens_render tree [] (by simp)
  have lexed := Silmaril.Formats.JsonWire.Internal.lex_tokens_eq
    (cs := text.toList) (off := 0) (Nat.lt_succ_self text.toList.length)
  rw [tokenized] at lexed
  obtain ⟨result, ran, tokens⟩ := Option.map_eq_some_iff.mp lexed
  have parsed : value? .rfc8259 (2 * result.tokens.length + 1) result.tokens =
      some (tree.mapScalar addFinite, []) := by
    rw [tokens]
    simpa using value?_printedTokens tree (2 * (printedTokens tree).length + 1) (by omega) []
  change parse? ⟨text.toUTF8⟩ = _
  simp [parse?, parseDecimal?, decode, fromResult, ran, parsed]
  exact mapNumbers_finite tree

end Silmaril.Proofs.Formats.JsonWire.Encoding
