module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical

open Assignment (LexicalBlock)
open Functions
open Lists (State Outcome)

local notation "Value" => Lists.Value

/-- Defaults use the defining block's lexical expression judgment.
The names label saved arguments and do not add bindings to this block. -/
inductive Elaborates (block : LexicalBlock) :
    List (String × Lowering.Resolve.SourceExpr) → List PlainPositionalDefault → Prop where
  | nil : Elaborates block [] []
  | cons {name : String} {source : Lowering.Resolve.SourceExpr} {code : Lowering.Expr} {reads : List Binding}
      {rest : List (String × Lowering.Resolve.SourceExpr)} {items : List PlainPositionalDefault} :
      Body.Operand block source code reads → Elaborates block rest items →
      Elaborates block ((name, source) :: rest) (⟨name, source, code, reads⟩ :: items)

/-- A reached error retains its heap without evaluating subsequent defaults. -/
inductive Evaluates (block : LexicalBlock) : State → List PlainPositionalDefault → Outcome (List Value) → Prop where
  | nil {state : State} : Evaluates block state [] (.ok [] state)
  | next {state middle : State} {item : PlainPositionalDefault} {rest : List PlainPositionalDefault}
      {value : Value} {out : Outcome (List Value)} :
      Body.Evaluates block state item.source item.value (.ok value middle) →
      Evaluates block middle rest out →
      Evaluates block state (item :: rest) (out.resume fun values final => .ok (value :: values) final)
  | failed {state final : State} {item : PlainPositionalDefault} {rest : List PlainPositionalDefault} {error : Lists.Error} :
      Body.Evaluates block state item.source item.value (.error error final) →
      Evaluates block state (item :: rest) (.error error final)

/-- Installation records the evaluated values and addresses from the
reached defining frame. That frame can own a binding or forward it. -/
inductive DefinesFor (block : LexicalBlock) (target : Binding) (id : Nat) (free : List FreeName)
    (keys : List Binding) (items : List PlainPositionalDefault) :
    State → Outcome Lists.Iteration.Flow → Prop where
  | failed {state final : State} {error : Lists.Error} :
      Evaluates block state items (.error error final) →
      DefinesFor block target id free keys items state (.error error final)
  | installed {state final : State} {values : List Value} {captures : List Lists.Capture} :
      Evaluates block state items (.ok values final) →
      Installs final free captures →
      DefinesFor block target id free keys items state
        (.ok .next (install target id captures (keys.zip values) final))

abbrev Defines (block : LexicalBlock) (target : Binding) (id : Nat) (free : List FreeName)
    (parameters : Parameters) :=
  DefinesFor block target id free (parameters.optional.map (fileSlot ∘ Prod.fst))

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical
