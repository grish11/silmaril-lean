module

public import Silmaril.Courses.Cambridge.L2.Concrete.Grammar
import Silmaril.Courses.Cambridge.Concrete.LexerProofs

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.Concrete

open Silmaril.Courses.Cambridge.Concrete

private theorem readType_tokens (type : Ty) (fuel : Nat) (suffix : List Token)
    (h : (typeTokens type).length ≤ fuel) :
    readType fuel (typeTokens type ++ suffix) = some (type, suffix) := by
  induction type generalizing fuel suffix <;> cases fuel <;>
    simp only [typeTokens, List.length_cons, List.length_nil, List.length_append] at h
  all_goals try omega
  case arr.succ domain codomain ihDomain ihCodomain fuel =>
    simp (discharger := omega) [typeTokens, List.append_assoc, readType, Cambridge.Concrete.expect,
      ihDomain fuel, ihCodomain fuel]
  all_goals rfl

/-- The lexical starts of rendered expressions. In particular, these do not
start the special keyword groups or end an infix or application group. -/
private def startsExpr : Token → Prop
  | .keyword .trueK | .keyword .falseK | .keyword .skip | .number _
  | .punct .minus | .punct .deref | .punct .openP | .variable _ => True
  | _ => False

private theorem termTokens_start (term : RawExpr) :
    ∃ head tail, termTokens term = head :: tail ∧ startsExpr head := by
  cases term with
  | int n => cases n <;> exact ⟨_, _, rfl, trivial⟩
  | bool b => cases b <;> exact ⟨_, _, rfl, trivial⟩
  | _ => exact ⟨_, _, rfl, trivial⟩

private theorem readGroup {fuel : Nat} {head : Token} {tail : List Token}
    (h : startsExpr head) :
    readExpr (fuel + 1) (.punct .openP :: head :: tail) =
      (do
        let (value, rest) ← readExpr fuel (head :: tail)
        finishGroup (readExpr fuel) value rest) := by
  cases head with
  | keyword k => cases k <;> first | exact h.elim | simp [readExpr]
  | punct p => cases p <;> first | exact h.elim | simp [readExpr]
  | _ => first | exact h.elim | simp [readExpr]

private theorem readGroup_tokens (term : RawExpr) (fuel : Nat) (suffix : List Token) :
    readExpr (fuel + 1) (.punct .openP :: (termTokens term ++ suffix)) =
      (do
        let (value, rest) ← readExpr fuel (termTokens term ++ suffix)
        finishGroup (readExpr fuel) value rest) := by
  obtain ⟨head, tail, h, hs⟩ := termTokens_start term
  rw [h, List.cons_append, readGroup hs]

private theorem finishGroup_application
    (read : List Token → Option (RawExpr × List Token)) (left term : RawExpr)
    (suffix : List Token) :
    finishGroup read left (termTokens term ++ suffix) =
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
  | int n =>
    cases n <;> cases fuel <;> first | rfl | (simp [termTokens] at h)
  | bool b => cases b <;> cases fuel <;> simp [termTokens, readExpr] at *
  | skip => cases fuel <;> simp [termTokens, readExpr] at *
  | deref name => cases fuel <;> simp [termTokens, readExpr] at *
  | var name => cases fuel <;> simp [termTokens, readExpr] at *
  | assign name value ih =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, Cambridge.Concrete.expect, ih]
  | binary left op right il ir =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · cases op <;> simp (discharger := omega) [termTokens, List.append_assoc, operator,
        readGroup_tokens, finishGroup, Cambridge.Concrete.expect, il, ir]
  | cond test yes no it iy ino =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, Cambridge.Concrete.expect, it, iy, ino]
  | seq left right il ir =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readGroup_tokens, finishGroup,
        Cambridge.Concrete.expect, il, ir]
  | loop test body it ib =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, Cambridge.Concrete.expect, it, ib]
  | lam name domain body ib =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, Cambridge.Concrete.expect,
        readType_tokens, ib]
  | app fn arg ihFn ihArg =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readGroup_tokens,
        finishGroup_application, Cambridge.Concrete.expect, ihFn, ihArg]
  | letE name type value body iv ib =>
    cases fuel <;> simp only [termTokens, List.length_append, List.length_cons, List.length_nil] at h
    · omega
    · simp (discharger := omega) [termTokens, List.append_assoc, readExpr, Cambridge.Concrete.expect,
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
      simp [termTokens, List.append_assoc, readExpr.eq_13, Cambridge.Concrete.expect,
        readType_tokens domain fuel _ hd, readType_tokens codomain fuel _ hc,
        iv fuel _ hv, ib fuel _ hb]

private def Spellable (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, Token.Spellable token

@[simp] private theorem spellable_nil : Spellable [] := List.forall_mem_nil _

@[simp] private theorem spellable_cons {token : Token} {tokens : List Token} :
    Spellable (token :: tokens) ↔ token.Spellable ∧ Spellable tokens :=
  List.forall_mem_cons

@[simp] private theorem spellable_append {left right : List Token} :
    Spellable (left ++ right) ↔ Spellable left ∧ Spellable right :=
  List.forall_mem_append

private theorem typeTokens_spellable (type : Ty) : Spellable (typeTokens type) := by
  induction type <;> simp [typeTokens, Token.Spellable, *]

private theorem termTokens_spellable {term : RawExpr} (h : NamesOk term) :
    Spellable (termTokens term) := by
  induction term with
  | int n => cases n <;> simp [termTokens, Token.Spellable]
  | bool b => cases b <;> simp [termTokens, Token.Spellable]
  | binary _ op _ _ _ =>
    cases op <;> simp_all [termTokens, NamesOk, operator, Token.Spellable]
  | _ =>
    simp_all [termTokens, NamesOk, Token.Spellable, typeTokens_spellable]

/-- The complete byte parser recovers every canonically printed source AST. -/
theorem parse_print (term : SourceExpr) : parse (print term) = some term.val := by
  unfold parse print
  rw [tokenize_render _ (termTokens_spellable term.property)]
  apply readWithPrecedence_of_grouped
  simpa only [List.append_nil] using
    readExpr_tokens term.val ((termTokens term.val).length + 1) [] (by omega)

theorem parseResolved_print (term : SourceExpr) :
    parseResolved (print term) = some (term.val.resolve []) := by
  simp [parseResolved, parse_print]

theorem print_injective : Function.Injective print := by
  intro left right h
  apply Subtype.ext
  exact Option.some.inj ((parse_print left).symm.trans ((congrArg parse h).trans (parse_print right)))

theorem parses_print (term : SourceExpr) : Parses (print term) term.val := parse_print term

theorem parseType_printType (type : Ty) : parseType (printType type) = some type := by
  unfold parseType printType
  rw [tokenize_render _ (typeTokens_spellable type)]
  apply readWithPrecedence_of_grouped
  simpa only [List.append_nil] using
    readType_tokens type ((typeTokens type).length + 1) [] (by omega)

theorem printType_injective : Function.Injective printType := by
  intro left right h
  exact Option.some.inj ((parseType_printType left).symm.trans
    ((congrArg parseType h).trans (parseType_printType right)))

end Silmaril.Courses.Cambridge.L2.Concrete
