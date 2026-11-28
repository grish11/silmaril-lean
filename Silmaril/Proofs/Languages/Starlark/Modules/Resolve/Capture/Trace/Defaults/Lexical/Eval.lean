module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Defs
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Site
import Silmaril.Languages.Starlark.Functions.Expressions.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (SourceExpr resolveTracked)
open Silmaril.Languages.Starlark.Lists (State Outcome Value)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

theorem append {block : LexicalBlock} {first second : List (String × SourceExpr)}
    {earlier later : List PlainPositionalDefault}
    (left : Elaborates block first earlier) (right : Elaborates block second later) :
    Elaborates block (first ++ second) (earlier ++ later) := by
  induction left with
  | nil => exact right
  | cons operand _ ih => exact .cons operand ih

theorem sources_eq {block : LexicalBlock} {source : List (String × SourceExpr)} {items : List PlainPositionalDefault}
    (related : Elaborates block source items) :
    items.map (fun item => (item.name, item.source)) = source := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem code_length {block : LexicalBlock} {source : List (String × SourceExpr)} {items : List PlainPositionalDefault}
    (related : Elaborates block source items) : (items.map PlainPositionalDefault.value).length = source.length := by
  simpa only [List.length_map] using congrArg List.length (sources_eq related)

theorem translated {block : LexicalBlock} {source : List (String × SourceExpr)} {items : List PlainPositionalDefault}
    (related : Elaborates block source items) :
    ∀ item ∈ items, resolveTracked block.context item.source = .ok (item.value, item.reads) := by
  induction related with
  | nil => simp
  | cons operand _ ih =>
    intro item present
    rcases List.mem_cons.mp present with rfl | later
    · exact Defaults.Body.resolves operand
    · exact ih item later

private theorem many_sound (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} {state : State} {items : List PlainPositionalDefault} {out : Outcome (List Value)}
    (evaluated : Evaluates block state items out) :
    Lowering.EvaluatesManyWith program available (fun _ _ _ => False) (fun _ => True)
      state (items.map PlainPositionalDefault.value) out := by
  induction evaluated with
  | nil => exact .empty
  | failed operand => exact .headError (Defaults.Body.evaluates _ _ operand)
  | @next _ _ _ _ _ out operand _ ih =>
    cases out with
    | error => exact .tailError (Defaults.Body.evaluates _ _ operand) ih
    | ok => exact .cons (Defaults.Body.evaluates _ _ operand) ih

theorem evaluates_agree (program : Program) (available : List DeclarationId)
    (bodyMeaning : Lowering.ClosureMeaning available) {block : LexicalBlock} {state : State}
    {items : List PlainPositionalDefault} {out : Outcome (List Value)}
    (ran : Evaluates block state items out) :
    (items.map PlainPositionalDefault.value).mapM (Lowering.denoteExprWith program available bodyMeaning) state = out :=
  Lowering.denoteExprsWith_eq_of_evaluatesMany (fun _ _ _ h => h.elim) (many_sound program available ran)

theorem unique {block : LexicalBlock} {state : State} {items : List PlainPositionalDefault}
    {first second : Outcome (List Value)}
    (a : Evaluates block state items first) (b : Evaluates block state items second) : first = second :=
  (evaluates_agree #[] [] (fun _ state => .error .notCallable state) a).symm.trans
    (evaluates_agree #[] [] (fun _ state => .error .notCallable state) b)

theorem total {block : LexicalBlock} {source : List (String × SourceExpr)} {items : List PlainPositionalDefault}
    (related : Elaborates block source items) (state : State) :
    ∃ out, Evaluates block state items out ∧ Defaults.Body.Extends state (finishState out) ∧
      (∀ values next, out = .ok values next → values.length = source.length) := by
  induction related generalizing state with
  | nil => exact ⟨_, .nil, ⟨rfl, fun _ _ cell => cell⟩, fun _ _ h => by cases h; rfl⟩
  | cons operand _ ih =>
    obtain ⟨one, first, keeps⟩ := Defaults.Body.operands_total operand state
    cases one with
    | error => exact ⟨_, .failed first, keeps, fun _ _ h => nomatch h⟩
    | ok value middle =>
      obtain ⟨out, tail, rest, count⟩ := ih middle
      have kept : Defaults.Body.Extends state (finishState out) :=
        ⟨rest.1.trans keeps.1, fun address cell stored => rest.2 address cell (keeps.2 address cell stored)⟩
      cases out with
      | error => exact ⟨_, .next first tail, kept, fun _ _ h => nomatch h⟩
      | ok values final => exact ⟨_, .next first tail, kept, fun _ _ h => by cases h; simp [count _ _ rfl]⟩

theorem evaluated_length {block : LexicalBlock} {source : List (String × SourceExpr)}
    {items : List PlainPositionalDefault} (related : Elaborates block source items)
    {state final : State} {values : List Value} (evaluated : Evaluates block state items (.ok values final)) :
    values.length = source.length := by
  obtain ⟨_, canonical, _, length⟩ := total related state
  exact length values final (unique canonical evaluated)

theorem evaluates_keeps {block : LexicalBlock} {source : List (String × SourceExpr)}
    {items : List PlainPositionalDefault} (related : Elaborates block source items) {state : State}
    {result : Outcome (List Value)} (evaluated : Evaluates block state items result) :
    Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Keeps state.heap.size state (finishState result) := by
  obtain ⟨_, canonical, extended, _⟩ := total related state
  rw [unique canonical evaluated] at extended
  exact ⟨extended.1, fun address cell _ found => extended.2 address cell found⟩

theorem defines_for_sound (program : Program) (available : List DeclarationId) (target : Binding)
    (id : Nat) (declaration : Declaration) {keys : List Binding}
    {block : LexicalBlock} {items : List PlainPositionalDefault}
    (found : program[id]? = some declaration)
    (defaultKeys : declaration.signature.defaulted.map Prod.fst = keys)
    (codes : declaration.signature.defaulted.map Prod.snd = items.map PlainPositionalDefault.value)
    {state : State} {out : Outcome Flow}
    (source : DefinesFor block target id declaration.free keys items state out) :
    Exec program available state (.define target id) out ∧ denoteBody program available (.define target id) state = out := by
  have operands {out : Outcome (List Value)} (evaluated : Evaluates block state items out) :
      ExecExprs program available state (defaultOperands program id) out := by
    have ordered : defaultOperands program id = items.map PlainPositionalDefault.value := by
      simp [defaultOperands, found, codes]
    rw [ordered]
    exact .evaluatesMany (calls := fun _ _ _ => False) (fun _ _ _ h => h.elim) (many_sound program available evaluated)
  have ran : Exec program available state (.define target id) out := by
    cases source with
    | failed evaluated => exact .define (operands evaluated)
    | installed evaluated captured =>
      have actual := Exec.define (target := target) (operands evaluated)
      simpa [Outcome.resume, define, found, Capture.installs_lookup _ captured, defaultKeys, install] using actual
  exact ⟨ran, (exec_iff_denoteBody _ _ _ _ _).mp ran⟩

theorem defines_for_total (program : Program) (available : List DeclarationId) (target : Binding)
    (id : Nat) (declaration : Declaration) {keys : List Binding}
    {block : LexicalBlock} {items : List PlainPositionalDefault}
    {expressions : List (String × SourceExpr)} (related : Elaborates block expressions items)
    (found : program[id]? = some declaration)
    (defaultKeys : declaration.signature.defaulted.map Prod.fst = keys)
    (codes : declaration.signature.defaulted.map Prod.snd = items.map PlainPositionalDefault.value)
    (state : State) (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (installed : Installs state declaration.free captures) :
    ∃ out, DefinesFor block target id declaration.free keys items state out ∧
      Exec program available state (.define target id) out ∧ denoteBody program available (.define target id) state = out ∧
      (∀ next, out = .ok .next next → ∃ final values, Evaluates block state items (.ok values final) ∧
        next = install target id captures (keys.zip values) final) := by
  obtain ⟨result, evaluated, kept, _⟩ := total related state
  have agreement {out : Outcome Flow} (ran : DefinesFor block target id declaration.free keys items state out) :
      Exec program available state (.define target id) out ∧ denoteBody program available (.define target id) state = out :=
    defines_for_sound program available target id declaration found defaultKeys codes ran
  cases result with
  | error error final =>
    have ran : DefinesFor block target id declaration.free keys items state (.error error final) := .failed evaluated
    exact ⟨_, ran, (agreement ran).1, (agreement ran).2, fun _ impossible => nomatch impossible⟩
  | ok values final =>
    let next := install target id captures (keys.zip values) final
    have ran : DefinesFor block target id declaration.free keys items state (.ok .next next) :=
      .installed evaluated (Silmaril.Languages.Starlark.Modules.Resolve.Capture.installs_in_same_slots kept.1 installed)
    exact ⟨_, ran, (agreement ran).1, (agreement ran).2, fun _ same =>
      ⟨final, values, evaluated, (EStateM.Result.ok.inj same).2.symm⟩⟩

theorem defines_sound (program : Program) (available : List DeclarationId) (target : Binding)
    (id : Nat) (parameters : Parameters) (declaration : Declaration)
    {block : LexicalBlock} {items : List PlainPositionalDefault}
    (related : Elaborates block parameters.optional items)
    (found : program[id]? = some declaration)
    (signature : declaration.signature = parameters.signature (items.map PlainPositionalDefault.value))
    {state : State} {out : Outcome Flow}
    (source : Defines block target id declaration.free parameters items state out) :
    Exec program available state (.define target id) out ∧ denoteBody program available (.define target id) state = out := by
  have length := code_length related
  have keys : declaration.signature.defaulted.map Prod.fst = parameters.optional.map (fileSlot ∘ Prod.fst) := by
    simp [signature, Defaults.signature_defaults, List.map_fst_zip, length]
  have codes : declaration.signature.defaulted.map Prod.snd = items.map PlainPositionalDefault.value := by
    simp [signature, Defaults.signature_defaults, List.map_snd_zip, length]
  exact defines_for_sound program available target id declaration found keys codes source

theorem defines_total (program : Program) (available : List DeclarationId) (target : Binding)
    (id : Nat) (parameters : Parameters) (declaration : Declaration)
    {block : LexicalBlock} {items : List PlainPositionalDefault}
    (related : Elaborates block parameters.optional items)
    (found : program[id]? = some declaration)
    (signature : declaration.signature = parameters.signature (items.map PlainPositionalDefault.value))
    (state : State) (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (installed : Installs state declaration.free captures) :
    ∃ out, Defines block target id declaration.free parameters items state out ∧
      Exec program available state (.define target id) out ∧ denoteBody program available (.define target id) state = out ∧
      (∀ next, out = .ok .next next → ∃ final values, Evaluates block state items (.ok values final) ∧
        next = install target id captures ((parameters.optional.map (fileSlot ∘ Prod.fst)).zip values) final) := by
  have length := code_length related
  have keys : declaration.signature.defaulted.map Prod.fst = parameters.optional.map (fileSlot ∘ Prod.fst) := by
    simp [signature, Defaults.signature_defaults, List.map_fst_zip, length]
  have codes : declaration.signature.defaulted.map Prod.snd = items.map PlainPositionalDefault.value := by
    simp [signature, Defaults.signature_defaults, List.map_snd_zip, length]
  exact defines_for_total program available target id declaration related found keys codes state captures installed

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical
