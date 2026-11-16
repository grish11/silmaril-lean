module

public import Silmaril.Logic.Egglog.Source.Named.Declarations.Thms
public import Silmaril.Logic.Egglog.Source.Named.Denotation.Defs
public import Mathlib.Data.List.OfFn

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named
open Silmaril.Logic.Institution.Examples

/-- Sequence an ordered finite dependent tuple without dropping a coordinate. -/
def sequence? : (n : Nat) → {β : Fin n → Type} →
    ((i : Fin n) → Option (β i)) → Option ((i : Fin n) → β i)
  | 0, _, _ => some (fun i => nomatch i)
  | n + 1, _, f => do
      let first ← f 0
      let rest ← sequence? n (fun i => f i.succ)
      pure (Fin.cases first rest)

abbrev ConstructorAt (D : Declarations) (n : Nat) :=
  Σ w : Fin n → D.LocalSort, Σ s : D.LocalSort, D.signature.Op n w s

abbrev RelationAt (D : Declarations) (n : Nat) :=
  Σ w : Fin n → D.LocalSort, D.signature.Rel n w

abbrev FunctionAt (D : Declarations) (n : Nat) :=
  Σ w : Fin n → D.LocalSort, Σ s : D.LocalSort, D.signature.Function n w s

/-- Lookup checks kind, spelling and exact arity; profile sorts come from the
checked declaration, rather than from occurrence-based guessing. -/
def constructor? (D : Declarations) (name : String) (n : Nat) :
    Option (ConstructorAt D n) :=
  D.data.constructors.attach.findSome? fun d =>
    if d.val.name = name then
      if h : d.val.inputs.length = n then by
        subst n
        have fields := D.valid.2.2.2.1 d.val (List.mem_append_left _ d.property)
        let w : Fin d.val.inputs.length → D.LocalSort :=
          fun i => ⟨d.val.inputs.get i, fields.2.1 _ (List.get_mem _ _)⟩
        let s : D.LocalSort := ⟨d.val.output, fields.2.2⟩
        exact some ⟨w, s, ⟨d.val, d.property, (List.ofFn_get _).symm, rfl⟩⟩
      else none
    else none

def relation? (D : Declarations) (name : String) (n : Nat) :
    Option (RelationAt D n) :=
  D.data.relations.attach.findSome? fun d =>
    if d.val.name = name then
      if h : d.val.inputs.length = n then by
        subst n
        have fields := D.valid.2.2.2.2 d.val d.property
        let w : Fin d.val.inputs.length → D.LocalSort :=
          fun i => ⟨d.val.inputs.get i, fields.2 _ (List.get_mem _ _)⟩
        exact some ⟨w, ⟨d.val, d.property, (List.ofFn_get _).symm⟩⟩
      else none
    else none

def function? (D : Declarations) (name : String) (n : Nat) :
    Option (FunctionAt D n) :=
  D.data.functions.attach.findSome? fun d =>
    if d.val.name = name then
      if h : d.val.inputs.length = n then by
        subst n
        have fields := D.valid.2.2.2.1 d.val (List.mem_append_right _ d.property)
        let w : Fin d.val.inputs.length → D.LocalSort :=
          fun i => ⟨d.val.inputs.get i, fields.2.1 _ (List.get_mem _ _)⟩
        let s : D.LocalSort := ⟨d.val.output, fields.2.2⟩
        exact some ⟨w, s, ⟨d.val, d.property, (List.ofFn_get _).symm, rfl⟩⟩
      else none
    else none

abbrev PackedTerm {D : Declarations} (Γ : CheckedContext D) :=
  Σ s : D.LocalSort, EQ.Term D.signature.toSignature Γ.profile s

/-- A checked cast tests only local finite names. -/
def termAt? {D : Declarations} {Γ : CheckedContext D} (s : D.LocalSort)
    (term : PackedTerm Γ) : Option (EQ.Term D.signature.toSignature Γ.profile s) :=
  if h : term.1 = s then some (h ▸ term.2) else none

/-- Structural recursion covers arbitrary nesting and arities. There is no
semantic fuel cap and no default value for a missing symbol or table row. -/
def resolveTerm? {D : Declarations} (Γ : CheckedContext D) :
    RawTerm → Option (PackedTerm Γ)
  | .var name => do
      let i ← (List.finRange Γ.bindings.length).find? fun i =>
        (Γ.bindings.get i).name == name
      pure ⟨Γ.profile i, .var i⟩
  | .app name n arguments => do
      let ⟨w, s, o⟩ ← constructor? D name n
      let values ← sequence? n (fun i => do
        let term ← resolveTerm? Γ (arguments i)
        termAt? (w i) term)
      pure ⟨s, .app o values⟩

def resolveAtom? {D : Declarations} (Γ : CheckedContext D) :
    RawAtom → Option (Core.Atom D.signature Γ.profile)
  | .equal left right => do
      let ⟨s, left⟩ ← resolveTerm? Γ left
      let right ← resolveTerm? Γ right
      let right ← termAt? s right
      pure (.equal ⟨s, left, right⟩)
  | .relation name n arguments => do
      let ⟨w, r⟩ ← relation? D name n
      let values ← sequence? n (fun i => do
        let term ← resolveTerm? Γ (arguments i)
        termAt? (w i) term)
      pure (.relation r values)
  | .row name n arguments value => do
      let ⟨w, s, f⟩ ← function? D name n
      let values ← sequence? n (fun i => do
        let term ← resolveTerm? Γ (arguments i)
        termAt? (w i) term)
      let value ← resolveTerm? Γ value
      let value ← termAt? s value
      pure (.row f values value)

def resolveSentence? (D : Declarations) : RawSentence → Option (Core.Sentence D.signature)
  | .rule context body head => do
      let Γ ← Context.check D context
      let body ← body.mapM (resolveAtom? Γ)
      let head ← resolveAtom? Γ head
      pure (.rule ⟨Γ.bindings.length, Γ.profile, body, head⟩)
  | .query context goals => do
      let Γ ← Context.check D context
      let goals ← goals.mapM (resolveAtom? Γ)
      pure (.query ⟨Γ.bindings.length, Γ.profile, goals⟩)

/-- Compilation retains the entire ordered program, including all queries. -/
def resolveProgram? (program : RawProgram) :
    Option (Σ D : Declarations, List (Core.Sentence D.signature)) := do
  let D ← checkDeclarations program.declarations
  let sentences ← program.sentences.mapM (resolveSentence? D)
  pure ⟨D, sentences⟩

end Silmaril.Logic.Egglog.Source.Named
