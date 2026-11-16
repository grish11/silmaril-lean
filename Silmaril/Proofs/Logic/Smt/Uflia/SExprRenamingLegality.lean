module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Defs
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Lexical.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming
open Silmaril.Logic.Smt.SExpr.Writer
variable {E F : Environment}

private theorem legal_children {es : List Expr} (h : LegalExpr (.list es)) :
    ∀ e ∈ es, LegalExpr e := by
  cases h with
  | list h => exact h

private theorem lookup_simple {E : Environment} {name : String}
    {i : Fin E.declarations.length} (h : lookup? E name = some i) :
    simpleSymbol name = true := by
  unfold lookup? at h
  split at h
  · rename_i hg
    have hguard : simpleSymbol name = true ∧ (!reserved.contains name) = true := by
      simpa only [Bool.and_eq_true] using hg
    exact hguard.1
  · contradiction

/-- Actual target lookup ensures that a renamed declared atom remains lexer-safe. -/
theorem NameMap.globalName_legal (f : NameMap E F) (name : String)
    (hname : LegalAtom name) : LegalAtom (globalName E f.rename name) := by
  unfold globalName
  cases hi : lookup? E name with
  | none => exact hname
  | some i => exact simpleSymbol_legalAtom _ (lookup_simple (f.lookup name i hi))

private theorem syntaxLocal_legal (locals : SyntaxLocals)
    (hlocals : ∀ name value, (name, value) ∈ locals → LegalExpr value)
    (name : String) (value : Expr) (h : syntaxLocal? locals name = some value) :
    LegalExpr value := by
  induction locals with
  | nil => simp [syntaxLocal?] at h
  | cons pair rest ih =>
    rcases pair with ⟨key, expression⟩
    simp only [syntaxLocal?] at h
    split at h
    · have hv : expression = value := Option.some.inj h
      subst value
      exact hlocals key expression (by simp)
    · exact ih (fun n v hv => hlocals n v (by simp [hv])) h

/-- Binding values are normalized in the caller's old scope. -/
theorem syntaxBindings_legal (recur : Expr → Option Expr)
    (hrecur : ∀ e output, LegalExpr e → recur e = some output → LegalExpr output)
    (bindings : List Expr) (values : SyntaxLocals)
    (hbindings : ∀ e ∈ bindings, LegalExpr e)
    (h : syntaxBindings? recur bindings = some values) :
    ∀ name value, (name, value) ∈ values → LegalExpr value := by
  induction bindings generalizing values with
  | nil =>
    simp only [syntaxBindings?] at h
    cases h
    simp
  | cons binding rest ih =>
    show ∀ name value, (name, value) ∈ values → LegalExpr value
    unfold syntaxBindings? at h
    split at h
    · contradiction
    · show ∀ name value, (name, value) ∈ values → LegalExpr value
      rename_i bs name expression tail heq
      obtain ⟨hb, hr⟩ : binding = .list [.atom name, expression] ∧ rest = tail :=
        List.cons.inj heq
      subst binding
      subst tail
      split at h
      · contradiction
      · show ∀ name value, (name, value) ∈ values → LegalExpr value
        change (recur expression).bind _ = some values at h
        obtain ⟨output, hout, h⟩ : ∃ output, recur expression = some output ∧
            (do let tail ← syntaxBindings? recur rest
                if tail.any (fun pair => pair.1 == name) then none
                else pure ((name, output) :: tail)) = some values := Option.bind_eq_some_iff.mp h
        obtain ⟨tail, htail, h⟩ : ∃ tail, syntaxBindings? recur rest = some tail ∧
            (if tail.any (fun pair => pair.1 == name) then none
             else some ((name, output) :: tail)) = some values := Option.bind_eq_some_iff.mp h
        split at h
        · contradiction
        · show ∀ name value, (name, value) ∈ values → LegalExpr value
          have hvalues : (name, output) :: tail = values := Option.some.inj h
          subst values
          have hbinding : ∀ e ∈ [.atom name, expression], LegalExpr e := legal_children (hbindings (.list [.atom name, expression]) (by simp))
          have hexpression : LegalExpr expression := hbinding expression (by simp)
          have houtput : LegalExpr output := hrecur expression output hexpression hout
          have hrest : ∀ n v, (n, v) ∈ tail → LegalExpr v := ih tail (fun e he => hbindings e (by simp [he])) htail
          intro n v hv
          rcases List.mem_cons.mp hv with heq | hmem
          · cases heq
            exact houtput
          · exact hrest n v hmem
    · contradiction

private theorem mapM_legal (recur : Expr → Option Expr)
    (hrecur : ∀ e output, LegalExpr e → recur e = some output → LegalExpr output)
    (inputs outputs : List Expr) (hsource : ∀ e ∈ inputs, LegalExpr e)
    (h : inputs.mapM recur = some outputs) : ∀ e ∈ outputs, LegalExpr e := by
  have hrelated := List.mapM_eq_some_iff_forall₂.mp h
  clear h
  revert hsource
  induction hrelated with
  | nil => simp
  | @cons source target sources targets hst hrel ihrel =>
    intro hs out hout
    rcases List.mem_cons.mp hout with heq | hmem
    · subst out
      exact hrecur source target (hs source (by simp)) hst
    · exact ihrel (fun e he => hs e (by simp [he])) out hmem

/-- Successful syntax normalization preserves the writer's actual atom legality.
The proof uses source legality and the stored local values, independently of
semantic decoder commutation. -/
theorem normalizeFuel_legal_of_names (rename : String → String)
    (names : ∀ name, LegalAtom name → LegalAtom (globalName E rename name))
    (fuel : Nat) (locals : SyntaxLocals)
    (e output : Expr) (hsource : LegalExpr e)
    (hlocals : ∀ name value, (name, value) ∈ locals → LegalExpr value)
    (h : normalizeFuel? E rename fuel locals e = some output) : LegalExpr output := by
  induction fuel generalizing locals e output with
  | zero => simp [normalizeFuel?] at h
  | succ fuel ih =>
    show LegalExpr output
    unfold normalizeFuel? at h
    split at h
    · cases h
      exact hsource
    · cases h
      exact hsource
    · show LegalExpr output
      rename_i name htrue hfalse
      cases hl : syntaxLocal? locals name with
      | some value =>
        simp only [hl] at h
        cases h
        exact syntaxLocal_legal locals hlocals name output hl
      | none =>
        show LegalExpr output
        simp only [hl] at h
        split at h
        · cases h
          exact hsource
        · cases h
          cases hsource with
          | atom ha => exact LegalExpr.atom (names name ha)
    · show LegalExpr output
      rename_i head bindings body
      change (syntaxBindings? (normalizeFuel? E rename fuel locals) (head :: bindings)).bind _ =
        some output at h
      obtain ⟨values, hvalues, hbody⟩ : ∃ values,
          syntaxBindings? (normalizeFuel? E rename fuel locals) (head :: bindings) = some values ∧
          normalizeFuel? E rename fuel (values ++ locals) body = some output :=
        Option.bind_eq_some_iff.mp h
      have hchildren : ∀ e ∈ [.atom "let", .list (head :: bindings), body], LegalExpr e :=
        legal_children hsource
      have hbindings : ∀ binding ∈ head :: bindings, LegalExpr binding :=
        legal_children (hchildren (.list (head :: bindings)) (by simp))
      have hlegalValues : ∀ name value, (name, value) ∈ values → LegalExpr value :=
        syntaxBindings_legal _
        (fun e out he ho => ih locals e out he hlocals ho) (head :: bindings) values hbindings hvalues
      have hbodyLegal : LegalExpr body := hchildren body (by simp)
      apply ih (values ++ locals) body output hbodyLegal _ hbody
      intro name value hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hlegalValues name value hv
      · exact hlocals name value hv
    · show LegalExpr output
      rename_i name arguments hnotlet
      split at h
      · contradiction
      · show LegalExpr output
        change (arguments.mapM (normalizeFuel? E rename fuel locals)).bind _ = some output at h
        obtain ⟨outputs, houtputs, h⟩ : ∃ outputs,
            arguments.mapM (normalizeFuel? E rename fuel locals) = some outputs ∧
            some (.list (.atom (globalName E rename name) :: outputs)) = some output :=
          Option.bind_eq_some_iff.mp h
        cases h
        have hchildren : ∀ e ∈ .atom name :: arguments, LegalExpr e := legal_children hsource
        have hname : LegalAtom name := by
          have hhead : LegalExpr (.atom name) := hchildren (.atom name) (by simp)
          cases hhead with
          | atom ha => exact ha
        apply LegalExpr.list
        intro child hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact LegalExpr.atom (names name hname)
        · exact mapM_legal _ (fun e out he ho => ih locals e out he hlocals ho)
            arguments outputs (fun e he => hchildren e (by simp [he])) houtputs child hc
    · contradiction

/-- The original fixed-sort interface follows from lexical name coherence. -/
theorem normalizeFuel_legal (f : NameMap E F) (fuel : Nat) (locals : SyntaxLocals)
    (e output : Expr) (hsource : LegalExpr e)
    (hlocals : ∀ name value, (name, value) ∈ locals → LegalExpr value)
    (h : normalizeFuel? E f.rename fuel locals e = some output) : LegalExpr output :=
  normalizeFuel_legal_of_names f.rename f.globalName_legal fuel locals e output hsource hlocals h

/-- Default-budget normalization also produces a writer-legal expression. -/
theorem normalize_legal (f : NameMap E F) (e output : Expr) (he : LegalExpr e)
    (h : normalize? E f.rename e = some output) : LegalExpr output :=
  normalizeFuel_legal f (expressionFuel e) [] e output he (by simp) h

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming
