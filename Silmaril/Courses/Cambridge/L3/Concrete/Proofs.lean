module

public import Silmaril.Courses.Cambridge.L3.Concrete.Grammar
import Silmaril.Courses.Cambridge.L3.Concrete.FieldProofs

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Concrete

open Silmaril.Courses.Cambridge.Concrete

private theorem readType_tokens (type : Ty) (fuel : Nat) (suffix : List Token)
    (h : (typeTokens type).length ≤ fuel) :
    readType fuel (typeTokens type ++ suffix) = some (type, suffix) := by
  induction type generalizing fuel suffix with
  | int | bool | unit =>
    cases fuel <;> first | rfl | (simp [typeTokens] at h)
  | arr left right il ir | prod left right il ir | sum left right il ir =>
    cases fuel <;> simp only [typeTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [typeTokens, List.append_assoc, readType, finishType, expect, il, ir]
  | ref contents ih =>
    cases fuel <;> simp only [typeTokens, List.length_append, List.length_cons] at h
    · omega
    · simp (discharger := omega) [typeTokens, List.append_assoc, readType, finishType, ih]
  | record labels fields ih =>
    cases fuel with
    | zero => simp [typeTokens] at h
    | succ fuel =>
      simp only [typeTokens, List.length_cons] at h
      simpa only [typeTokens, List.cons_append, readType] using
        readRecord_print_bounded Ty.record (readType fuel) typeTokens .colon labels fields
          fuel suffix (by omega) (fun i tail bound => ih i fuel tail bound)

/-- Comparing canonical type tokens compares the types, including record order. -/
theorem typeTokens_injective : Function.Injective typeTokens := by
  intro left right h
  have hl := readType_tokens left (typeTokens left).length [] (Nat.le_refl _)
  have hr := readType_tokens right (typeTokens right).length [] (Nat.le_refl _)
  rw [h] at hl
  exact congrArg Prod.fst (Option.some.inj (hl.symm.trans hr))

private def startsExpr : Token → Prop
  | .keyword .trueK | .keyword .falseK | .keyword .skip | .number _ | .location _ | .variable _
  | .punct .minus | .punct .deref | .punct .openP | .punct .openBrace
  | .keyword (.data .fst) | .keyword (.data .snd) | .keyword (.data .ref) => True
  | _ => False

private theorem termTokens_start (term : RawExpr) :
    ∃ head tail, termTokens term = head :: tail ∧ startsExpr head := by
  cases term with
  | int n => cases n <;> exact ⟨_, _, rfl, trivial⟩
  | bool b => cases b <;> exact ⟨_, _, rfl, trivial⟩
  | loc address => exact ⟨_, _, rfl, trivial⟩
  | _ => exact ⟨_, _, rfl, trivial⟩

private theorem readGroup {fuel : Nat} {head : Token} {tail : List Token}
    (h : startsExpr head) :
    readExpr (fuel + 1) (.punct .openP :: head :: tail) =
      (do
        let (value, rest) ← readExpr fuel (head :: tail)
        finishExpr (readExpr fuel) value rest) := by
  cases head with
  | keyword k =>
    cases k with
    | data k => cases k <;> first | exact h.elim | simp [readExpr]
    | _ => first | exact h.elim | simp [readExpr]
  | punct p => cases p <;> first | exact h.elim | simp [readExpr]
  | _ => simp [readExpr]

private theorem readGroup_tokens (term : RawExpr) (fuel : Nat) (suffix : List Token) :
    readExpr (fuel + 1) (.punct .openP :: (termTokens term ++ suffix)) =
      (do
        let (value, rest) ← readExpr fuel (termTokens term ++ suffix)
        finishExpr (readExpr fuel) value rest) := by
  obtain ⟨head, tail, h, hs⟩ := termTokens_start term
  rw [h, List.cons_append, readGroup hs]

private theorem finishExpr_application
    (read : List Token → Option (RawExpr × List Token)) (left term : RawExpr)
    (suffix : List Token) :
    finishExpr read left (termTokens term ++ suffix) =
      (do
        let (right, tail) ← read (termTokens term ++ suffix)
        let tail ← expect (.punct .closeP) tail
        return (.app left right, tail)) := by
  obtain ⟨head, tail, h, hs⟩ := termTokens_start term
  rw [h, List.cons_append]
  cases head with
  | punct p => cases p <;> first | exact hs.elim | rfl
  | _ => rfl

private theorem readExpr_tokens (term : RawExpr) (fuel : Nat) (suffix : List Token)
    (h : (termTokens term).length ≤ fuel) :
    readExpr fuel (termTokens term ++ suffix) = some (term, suffix) := by
  induction term generalizing fuel suffix with
  | int n => cases n <;> cases fuel <;> first | rfl | (simp [termTokens] at h)
  | bool b => cases b <;> cases fuel <;> first | rfl | (simp [termTokens] at h)
  | skip | var =>
    cases fuel <;> first | rfl | (simp [termTokens] at h)
  | loc address =>
    cases fuel with
    | zero => simp [termTokens] at h
    | succ fuel => simp [termTokens, addressToken, readExpr, readAddress_addressChars]
  | deref value ih | ref value ih | fst value ih | snd value ih =>
    cases fuel <;> simp only [termTokens, List.length_cons] at h
    · omega
    · simp (discharger := omega) [termTokens, readExpr, ih]
  | binary left op right il ir =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · cases op <;> simp (discharger := omega) [termTokens, List.append_assoc, operator,
        readGroup_tokens, finishExpr, finishExpr.binary, expect, il, ir]
  | assign left right il ir | seq left right il ir | pair left right il ir =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readGroup_tokens,
        finishExpr, finishExpr.binary, expect, il, ir]
  | app fn arg ihFn ihArg =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readGroup_tokens,
        finishExpr_application, expect, ihFn, ihArg]
  | project value label ih =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readGroup_tokens, finishExpr, ih]
  | cond test yes no it iy ino =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, expect, it, iy, ino]
  | loop test body it ib =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, expect, it, ib]
  | lam name domain body ib =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, expect,
        readType_tokens, ib]
  | letE name type value body iv ib =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, expect,
        readType_tokens, iv, ib]
  | letRecFun fn param domain codomain value body iv ib =>
    cases fuel with
    | zero => simp [termTokens] at h
    | succ fuel =>
      simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
      have hd : (typeTokens domain).length ≤ fuel := by omega
      have hc : (typeTokens codomain).length ≤ fuel := by omega
      have hv : (termTokens value).length ≤ fuel := by omega
      have hb : (termTokens body).length ≤ fuel := by omega
      simp [termTokens, List.append_assoc, readExpr, expect,
        readType_tokens domain fuel _ hd, readType_tokens codomain fuel _ hc,
        iv fuel _ hv, ib fuel _ hb]
  | inl value type ih | inr value type ih =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, expect,
        readType_tokens, ih]
  | matchSum value x typeX left y typeY right iv il ir =>
    cases fuel with
    | zero => simp [termTokens] at h
    | succ fuel =>
      simp only [termTokens, branchTokens, List.length_append, List.length_cons, List.length_nil] at h
      have hv : (termTokens value).length ≤ fuel := by omega
      have hx : (typeTokens typeX).length ≤ fuel := by omega
      have hy : (typeTokens typeY).length ≤ fuel := by omega
      have hl : (termTokens left).length ≤ fuel := by omega
      have hr : (termTokens right).length ≤ fuel := by omega
      simp [termTokens, branchTokens, List.append_assoc, readExpr, readBranch, expect,
        readType_tokens typeX fuel _ hx, readType_tokens typeY fuel _ hy,
        iv fuel _ hv, il fuel _ hl, ir fuel _ hr]
  | record labels fields ih =>
    cases fuel with
    | zero => simp [termTokens] at h
    | succ fuel =>
      simp only [termTokens, List.length_cons] at h
      simpa only [termTokens, List.cons_append, readExpr] using
        readRecord_print_bounded RawExpr.record (readExpr fuel) termTokens .equals labels fields
          fuel suffix (by omega) (fun i tail bound => ih i fuel tail bound)

private theorem typeTokens_spelled {type : Ty} (h : TypeNamesOk type) :
    TokensSpelled (typeTokens type) := by
  induction type with
  | record labels fields ih =>
    simp only [typeTokens, tokensSpelled_cons, spell_punct, true_and]
    exact recordTokens_spelled .colon labels _ (fun i => ⟨(h i).1, ih i (h i).2⟩)
  | _ => simp_all [typeTokens, TypeNamesOk]

private theorem termTokens_spelled {term : RawExpr} (h : NamesOk term) :
    TokensSpelled (termTokens term) := by
  induction term with
  | int n => cases n <;> simp [termTokens]
  | bool b => cases b <;> simp [termTokens]
  | binary _ op _ _ _ =>
    cases op <;> simp_all [termTokens, NamesOk, operator]
  | record labels fields ih =>
    simp only [termTokens, tokensSpelled_cons, spell_punct, true_and]
    exact recordTokens_spelled .equals labels _ (fun i => ⟨(h i).1, ih i (h i).2⟩)
  | _ => simp_all [termTokens, branchTokens, NamesOk, typeTokens_spelled]

theorem parse_print (term : SourceExpr) : parse (print term) = some term.val := by
  unfold parse print
  rw [lex_renderL3 _ (termTokens_spelled term.property)]
  apply readWithPrecedence_of_grouped
  simpa only [List.append_nil] using
    readExpr_tokens term.val ((termTokens term.val).length + 1) [] (by omega)

theorem parses_print (term : SourceExpr) : Parses (print term) term.val := parse_print term

theorem parseResolved_print (term : SourceExpr) :
    parseResolved (print term) = some (term.val.resolve []) := by
  simp [parseResolved, parse_print]

theorem print_injective : Function.Injective print := by
  intro left right h
  apply Subtype.ext
  exact Option.some.inj ((parse_print left).symm.trans ((congrArg parse h).trans (parse_print right)))

theorem parseType_printType (type : SourceType) : parseType (printType type) = some type.val := by
  unfold parseType printType
  rw [lex_renderL3 _ (typeTokens_spelled type.property)]
  apply readWithPrecedence_of_grouped
  simpa only [List.append_nil] using
    readType_tokens type.val ((typeTokens type.val).length + 1) [] (by omega)

theorem printType_injective : Function.Injective printType := by
  intro left right h
  apply Subtype.ext
  exact Option.some.inj ((parseType_printType left).symm.trans
    ((congrArg parseType h).trans (parseType_printType right)))

end Silmaril.Courses.Cambridge.L3.Concrete
