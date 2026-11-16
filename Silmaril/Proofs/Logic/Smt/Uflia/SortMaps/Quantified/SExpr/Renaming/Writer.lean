module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Names.Thms
public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Legality.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Legality.Thms
public import Silmaril.Logic.Smt.SExpr.Reader.Thms
public import Silmaril.Logic.Smt.SExpr.Writer.Thms

/-! Writer legality is independent of decoder commutation. Every source atom
comes from the actual reader, a fresh binder, or coherent target declaration
lookup. The final wrapper retains the actual executable transformed expression. -/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open Silmaril.Logic.Smt.Uflia.SExpr
open Uflia.Quantified.SExpr (ByteAccepted decodeSentence?)
open Silmaril.Logic.Smt.SExpr.Writer
variable {E F : Environment}

private theorem children_legal {es : List Expr} (legal : LegalExpr (.list es)) :
    ∀ e ∈ es, LegalExpr e := by
  cases legal with
  | list h => exact h

private theorem pair_legal {a b : Expr} (ha : LegalExpr a) (hb : LegalExpr b) :
    LegalExpr (.list [a, b]) := by
  apply LegalExpr.list
  intro e member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ha
  · exact hb

private theorem triple_legal {a b c : Expr}
    (ha : LegalExpr a) (hb : LegalExpr b) (hc : LegalExpr c) :
    LegalExpr (.list [a, b, c]) := by
  apply LegalExpr.list
  intro e member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

/-- The generic open traversal needs legal spellings for preexisting target
locals. At the public closed entry this invariant is discharged by the empty scope. -/
def ScopeLegal (scope : Scope) : Prop := ∀ pair ∈ scope, LegalAtom pair.2

private theorem scopeLegal_append {left right : Scope}
    (hl : ScopeLegal left) (hr : ScopeLegal right) : ScopeLegal (left ++ right) := by
  intro pair member
  rcases List.mem_append.mp member with member | member
  · exact hl pair member
  · exact hr pair member

private theorem scopeLegal_reverse {scope : Scope} (h : ScopeLegal scope) :
    ScopeLegal scope.reverse := by
  intro pair member
  exact h pair (List.mem_reverse.mp member)

private theorem localName_legal (scope : Scope) (legal : ScopeLegal scope)
    (name target : String) (found : localName? scope name = some target) : LegalAtom target := by
  induction scope with
  | nil => simp [localName?, Uflia.Quantified.SExpr.Renaming.localName?] at found
  | cons pair rest ih =>
    rcases pair with ⟨source, value⟩
    simp only [localName?, Uflia.Quantified.SExpr.Renaming.localName?] at found
    split at found
    · cases found
      exact legal (source, target) (by simp)
    · exact ih (fun pair member => legal pair (List.mem_cons_of_mem _ member)) found

private theorem global_legal (f : NameMap E F) (name : String)
    (legal : LegalAtom name) {i : Fin E.declarations.length}
    (found : lookup? E name = some i) : LegalAtom (f.rename name) := by
  have h := f.toNameMap.globalName_legal name legal
  simpa only [Uflia.SExpr.Renaming.globalName, found] using h

/-- Every admitted canonical sort atom is legal for the concrete writer. -/
theorem sortExpr_legal (sort : SortCode String)
    (admitted : F.sort? (sortExpr sort) = some sort) : LegalExpr (sortExpr sort) := by
  cases sort with
  | bool => exact .atom (Uflia.SExpr.Renaming.simpleSymbol_legalAtom _ (by decide))
  | int => exact .atom (Uflia.SExpr.Renaming.simpleSymbol_legalAtom _ (by decide))
  | user name =>
    have lexical : simpleSymbol name = true := by
      by_cases hb : name = "Bool"
      · subst name; decide
      · by_cases hi : name = "Int"
        · subst name; decide
        · simp only [sortExpr, Environment.sort?] at admitted
          split at admitted
          · rename_i h
            exact (Bool.and_eq_true_iff.mp h).1
          · contradiction
    exact .atom (Uflia.SExpr.Renaming.simpleSymbol_legalAtom name lexical)

/-- Freshening emits the actual mapped sort atoms and legal fresh names.
Repeated quantifier names remain available to the lexical shadowing rules. -/
theorem renameBinders_legal (f : NameMap E F) (next : Nat) (bindings : List Expr)
    (renamed : List Expr) (scope : Scope)
    (sourceLegal : ∀ e ∈ bindings, LegalExpr e)
    (success : renameBinders? f next bindings = some (renamed, scope)) :
    (∀ e ∈ renamed, LegalExpr e) ∧ ScopeLegal scope := by
  induction bindings generalizing next renamed scope with
  | nil =>
    simp only [renameBinders?] at success
    cases success
    exact ⟨by simp, by simp [ScopeLegal]⟩
  | cons binding rest ih =>
    unfold renameBinders? at success
    split at success
    · contradiction
    · rename_i allocation next input name sort tail same
      obtain ⟨hb, hr⟩ : binding = .list [.atom name, sort] ∧ rest = tail := List.cons.inj same
      subst binding
      subst tail
      split at success
      · contradiction
      · change (E.sort? sort).bind _ = some (renamed, scope) at success
        obtain ⟨sortCode, hsort, success⟩ := Option.bind_eq_some_iff.mp success
        change (renameBinders? f (allocation + 1) rest).bind _ = some (renamed, scope) at success
        obtain ⟨pair, hrest, success⟩ := Option.bind_eq_some_iff.mp success
        rcases pair with ⟨renamedRest, scopeRest⟩
        cases success
        obtain ⟨legalRest, legalScope⟩ := ih (allocation + 1) renamedRest scopeRest
          (fun e member => sourceLegal e (List.mem_cons_of_mem _ member)) hrest
        have legalSort : LegalExpr (sortExpr (f.abstract.sorts sortCode)) :=
          sortExpr_legal _ (f.sorts sort sortCode hsort)
        constructor
        · intro e member
          rcases List.mem_cons.mp member with rfl | member
          · exact pair_legal (.atom (freshName_legal allocation)) legalSort
          · exact legalRest e member
        · intro pair member
          rcases List.mem_cons.mp member with same | member
          · cases same
            exact freshName_legal allocation
          · exact legalScope pair member
    · contradiction

/-- Every RHS is handled by the same old-scope recursion; new binding spellings
are legal independently of the original duplicate-name rejection check. -/
theorem renameBindings_legal (recur : Expr → Option Expr)
    (recurLegal : ∀ e output, LegalExpr e → recur e = some output → LegalExpr output)
    (next : Nat) (bindings renamed : List Expr) (scope : Scope)
    (sourceLegal : ∀ e ∈ bindings, LegalExpr e)
    (success : renameBindings? recur next bindings = some (renamed, scope)) :
    (∀ e ∈ renamed, LegalExpr e) ∧ ScopeLegal scope := by
  induction bindings generalizing next renamed scope with
  | nil =>
    simp only [renameBindings?, Uflia.Quantified.SExpr.Renaming.renameBindings?] at success
    cases success
    exact ⟨by simp, by simp [ScopeLegal]⟩
  | cons binding rest ih =>
    unfold renameBindings? Uflia.Quantified.SExpr.Renaming.renameBindings? at success
    split at success
    · contradiction
    · rename_i allocation next input name value tail same
      obtain ⟨hb, hr⟩ : binding = .list [.atom name, value] ∧ rest = tail := List.cons.inj same
      subst binding
      subst tail
      split at success
      · contradiction
      · change (recur value).bind _ = some (renamed, scope) at success
        obtain ⟨output, houtput, success⟩ := Option.bind_eq_some_iff.mp success
        change (renameBindings? recur (allocation + 1) rest).bind _ = some (renamed, scope) at success
        obtain ⟨pair, hrest, success⟩ := Option.bind_eq_some_iff.mp success
        rcases pair with ⟨renamedRest, scopeRest⟩
        change (if scopeRest.any (fun pair => pair.1 == name) then none
          else some (.list [.atom (freshName allocation), output] :: renamedRest,
            (name, freshName allocation) :: scopeRest)) = some (renamed, scope) at success
        split at success
        · contradiction
        · cases success
          obtain ⟨legalRest, legalScope⟩ := ih (allocation + 1) renamedRest scopeRest
            (fun e member => sourceLegal e (List.mem_cons_of_mem _ member)) hrest
          have legalValue : LegalExpr value :=
            children_legal (sourceLegal (.list [.atom name, value]) (by simp)) value (by simp)
          constructor
          · intro e member
            rcases List.mem_cons.mp member with rfl | member
            · exact pair_legal (.atom (freshName_legal allocation))
                (recurLegal value output legalValue houtput)
            · exact legalRest e member
          · intro pair member
            rcases List.mem_cons.mp member with same | member
            · cases same
              exact freshName_legal allocation
            · exact legalScope pair member
    · contradiction

private theorem mapM_legal (recur : Expr → Option Expr)
    (recurLegal : ∀ e output, LegalExpr e → recur e = some output → LegalExpr output)
    (inputs outputs : List Expr) (sourceLegal : ∀ e ∈ inputs, LegalExpr e)
    (success : inputs.mapM recur = some outputs) : ∀ e ∈ outputs, LegalExpr e := by
  have related := List.mapM_eq_some_iff_forall₂.mp success
  clear success
  revert sourceLegal
  induction related with
  | nil => simp
  | @cons source target sources targets hs related ih =>
    intro legal e member
    rcases List.mem_cons.mp member with rfl | member
    · exact recurLegal source e (legal source (by simp)) hs
    · exact ih (fun e member => legal e (List.mem_cons_of_mem _ member)) e member

/-- Full-syntax successful traversal is writer-legal for every original legal
source expression and every legal target scope. No decoder theorem is assumed. -/
theorem renameScopedFuel_legal (f : NameMap E F) (fuel : Nat) (scope : Scope) (next : Nat)
    (expression output : Expr) (sourceLegal : LegalExpr expression) (scopeLegal : ScopeLegal scope)
    (success : renameScopedFuel? f fuel scope next expression = some output) : LegalExpr output := by
  induction fuel generalizing scope next expression output with
  | zero => simp [renameScopedFuel?] at success
  | succ fuel ih =>
    unfold renameScopedFuel? at success
    split at success
    · cases success
      exact sourceLegal
    · cases success
      exact sourceLegal
    · rename_i name htrue hfalse
      cases found : localName? scope name with
      | some target =>
        simp only [found] at success
        cases success
        exact .atom (localName_legal scope scopeLegal name target found)
      | none =>
        simp only [found] at success
        split at success
        · cases success
          exact sourceLegal
        · change (lookup? E name).bind _ = some output at success
          obtain ⟨index, hindex, success⟩ := Option.bind_eq_some_iff.mp success
          cases success
          cases sourceLegal with
          | atom legal => exact .atom (global_legal f name legal hindex)
    · rename_i head bindings body
      change (renameBinders? f next (head :: bindings)).bind _ = some output at success
      obtain ⟨pair, hbinders, success⟩ := Option.bind_eq_some_iff.mp success
      rcases pair with ⟨renamed, added⟩
      change (renameScopedFuel? f fuel (added.reverse ++ scope)
        (next + (head :: bindings).length) body).bind _ = some output at success
      obtain ⟨bodyOutput, hbody, success⟩ := Option.bind_eq_some_iff.mp success
      cases success
      have children := children_legal sourceLegal
      obtain ⟨legalBinders, legalAdded⟩ := renameBinders_legal f next (head :: bindings) renamed added
        (children_legal (children (.list (head :: bindings)) (by simp))) hbinders
      exact triple_legal (children (.atom "forall") (by simp)) (.list legalBinders)
        (ih _ _ body bodyOutput (children body (by simp))
          (scopeLegal_append (scopeLegal_reverse legalAdded) scopeLegal) hbody)
    · rename_i head bindings body
      change (renameBinders? f next (head :: bindings)).bind _ = some output at success
      obtain ⟨pair, hbinders, success⟩ := Option.bind_eq_some_iff.mp success
      rcases pair with ⟨renamed, added⟩
      change (renameScopedFuel? f fuel (added.reverse ++ scope)
        (next + (head :: bindings).length) body).bind _ = some output at success
      obtain ⟨bodyOutput, hbody, success⟩ := Option.bind_eq_some_iff.mp success
      cases success
      have children := children_legal sourceLegal
      obtain ⟨legalBinders, legalAdded⟩ := renameBinders_legal f next (head :: bindings) renamed added
        (children_legal (children (.list (head :: bindings)) (by simp))) hbinders
      exact triple_legal (children (.atom "exists") (by simp)) (.list legalBinders)
        (ih _ _ body bodyOutput (children body (by simp))
          (scopeLegal_append (scopeLegal_reverse legalAdded) scopeLegal) hbody)
    · rename_i head bindings body
      change (renameBindings? (renameScopedFuel? f fuel scope next) next (head :: bindings)).bind _ =
        some output at success
      obtain ⟨pair, hbindings, success⟩ := Option.bind_eq_some_iff.mp success
      rcases pair with ⟨renamed, added⟩
      change (renameScopedFuel? f fuel (added ++ scope)
        (next + (head :: bindings).length) body).bind _ = some output at success
      obtain ⟨bodyOutput, hbody, success⟩ := Option.bind_eq_some_iff.mp success
      cases success
      have children := children_legal sourceLegal
      obtain ⟨legalBindings, legalAdded⟩ := renameBindings_legal _
        (fun e out legal result => ih scope next e out legal scopeLegal result)
        next (head :: bindings) renamed added
        (children_legal (children (.list (head :: bindings)) (by simp))) hbindings
      exact triple_legal (children (.atom "let") (by simp)) (.list legalBindings)
        (ih _ _ body bodyOutput (children body (by simp))
          (scopeLegal_append legalAdded scopeLegal) hbody)
    · rename_i name arguments hforall hexists hlet
      have children := children_legal sourceLegal
      have headLegal : LegalAtom name := by
        cases children (.atom name) (by simp) with
        | atom h => exact h
      split at success
      · change (arguments.mapM (renameScopedFuel? f fuel scope next)).bind _ = some output at success
        obtain ⟨outputs, houtputs, success⟩ := Option.bind_eq_some_iff.mp success
        cases success
        exact .list (by
          intro e member
          rcases List.mem_cons.mp member with rfl | member
          · exact .atom headLegal
          · exact mapM_legal _ (fun e out legal result => ih scope next e out legal scopeLegal result)
              arguments outputs (fun e member => children e (List.mem_cons_of_mem _ member))
              houtputs e member)
      · split at success
        · contradiction
        · change (lookup? E name).bind _ = some output at success
          obtain ⟨index, hindex, success⟩ := Option.bind_eq_some_iff.mp success
          change (arguments.mapM (renameScopedFuel? f fuel scope next)).bind _ = some output at success
          obtain ⟨outputs, houtputs, success⟩ := Option.bind_eq_some_iff.mp success
          cases success
          exact .list (by
            intro e member
            rcases List.mem_cons.mp member with rfl | member
            · exact .atom (global_legal f name headLegal hindex)
            · exact mapM_legal _ (fun e out legal result => ih scope next e out legal scopeLegal result)
                arguments outputs (fun e member => children e (List.mem_cons_of_mem _ member))
                houtputs e member)
    · contradiction

/-- Closed executable entry needs no extra scope/freshness premise. -/
theorem rename_legal (f : NameMap E F) (expression output : Expr) (sourceLegal : LegalExpr expression)
    (success : rename? f expression = some output) : LegalExpr output :=
  renameScopedFuel_legal f (expressionFuel expression) [] (firstFresh F) expression output
    sourceLegal (by simp [ScopeLegal]) success

/-- The actual transformed expression is read back from its rendered bytes. -/
theorem rename_read_render (f : NameMap E F) (a : ByteAccepted E) (output : Expr)
    (success : rename? f a.expression = some output) :
    Silmaril.Logic.Smt.readForms (render output) = some [output] := by
  have sourceLegal : LegalExpr a.expression :=
    Silmaril.Logic.Smt.SExpr.Writer.readForms_legal a.bytes [a.expression] a.reads a.expression (by simp)
  exact read_render output (rename_legal f a.expression output sourceLegal success)

/-- Extract only from the actual executable successful transformation. -/
def ByteAccepted.renamedExpression (a : ByteAccepted E) (f : NameMap E F)
    (success : ∃ output, rename? f a.expression = some output) : Expr :=
  (rename? f a.expression).get (by rcases success with ⟨output, h⟩; simp only [h, Option.isSome_some])

theorem ByteAccepted.renamedExpression_spec (a : ByteAccepted E) (f : NameMap E F)
    (success : ∃ output, rename? f a.expression = some output) :
    rename? f a.expression = some (ByteAccepted.renamedExpression a f success) := by
  exact (Option.some_get _).symm

/-- Decoder success is supplied by the independent scoped-commutation theorem;
writer legality and both actual executable byte boundaries are proved here. -/
def ByteAccepted.rename (a : ByteAccepted E) (f : NameMap E F)
    (success : ∃ output, rename? f a.expression = some output ∧
      decodeSentence? F output = some (Hom.quantifiedSentence f.abstract a.sentence)) : ByteAccepted F := by
  let present : ∃ output, rename? f a.expression = some output :=
    let ⟨output, renamed, _⟩ := success; ⟨output, renamed⟩
  let output := ByteAccepted.renamedExpression a f present
  have renamed : rename? f a.expression = some output := ByteAccepted.renamedExpression_spec a f present
  have decoded : decodeSentence? F output = some (Hom.quantifiedSentence f.abstract a.sentence) := by
    obtain ⟨actual, hactual, decoded⟩ := success
    have same : output = actual := Option.some.inj (renamed.symm.trans hactual)
    simpa only [same] using decoded
  exact ⟨⟨output, Hom.quantifiedSentence f.abstract a.sentence, decoded⟩, render output,
    rename_read_render f a output renamed⟩

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
