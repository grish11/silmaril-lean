module

public import Silmaril.Logic.Egglog.Source.Named.Representation.Defs
public import Silmaril.Logic.Egglog.Source.Named.Resolution.Thms
public import Silmaril.Logic.Egglog.Source.Named.Parser.Thms
public import Mathlib.Data.List.FinRange

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named
open CategoryTheory Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Lookup is defined for each declared constructor, at its actual declaration arity. -/
theorem constructor?_exists (D : Declarations) (declaration : TotalDeclaration)
    (member : declaration ∈ D.data.constructors) :
    ∃ result : ConstructorAt D declaration.inputs.length,
      constructor? D declaration.name declaration.inputs.length = some result := by
  cases found : constructor? D declaration.name declaration.inputs.length with
  | none =>
      unfold constructor? at found
      have missing := (List.findSome?_eq_none_iff.mp found)
        ⟨declaration, member⟩ (by simp)
      simp at missing
  | some result => exact ⟨result, rfl⟩

/-- Every declared constructor is found at its exact full profile. -/
theorem constructor?_complete {D : Declarations} {n : Nat} {w : Fin n → D.LocalSort} {s : D.LocalSort}
    (symbol : D.signature.Op n w s) :
    constructor? D symbol.val.name n = some ⟨w, s, symbol⟩ := by
  have arity : symbol.val.inputs.length = n := by
    rw [symbol.property.2.1, List.length_ofFn]
  have existsAt (k : Nat) (same : symbol.val.inputs.length = k) :
      ∃ result : ConstructorAt D k, constructor? D symbol.val.name k = some result := by
    subst k
    exact constructor?_exists D symbol.val symbol.property.1
  obtain ⟨result, found⟩ := existsAt n arity
  rcases result with ⟨profile, output, other⟩
  have named := constructor?_name D symbol.val.name n _ found
  obtain ⟨sameProfile, sameOutput, sameSymbol⟩ :=
    constructor_profile_unique symbol other named.symm
  subst profile
  subst output
  have equal : symbol = other := eq_of_heq sameSymbol
  subst other
  exact found

/-- Lookup is defined for each declared relation, at its actual declaration arity. -/
theorem relation?_exists (D : Declarations) (declaration : RelationDeclaration)
    (member : declaration ∈ D.data.relations) :
    ∃ result : RelationAt D declaration.inputs.length,
      relation? D declaration.name declaration.inputs.length = some result := by
  cases found : relation? D declaration.name declaration.inputs.length with
  | none =>
      unfold relation? at found
      have missing := (List.findSome?_eq_none_iff.mp found)
        ⟨declaration, member⟩ (by simp)
      simp at missing
  | some result => exact ⟨result, rfl⟩

/-- Every declared relation is found at its exact full profile. -/
theorem relation?_complete {D : Declarations} {n : Nat} {w : Fin n → D.LocalSort}
    (symbol : D.signature.Rel n w) :
    relation? D symbol.val.name n = some ⟨w, symbol⟩ := by
  have arity : symbol.val.inputs.length = n := by
    rw [symbol.property.2, List.length_ofFn]
  have existsAt (k : Nat) (same : symbol.val.inputs.length = k) :
      ∃ result : RelationAt D k, relation? D symbol.val.name k = some result := by
    subst k
    exact relation?_exists D symbol.val symbol.property.1
  obtain ⟨result, found⟩ := existsAt n arity
  rcases result with ⟨profile, other⟩
  have named := relation?_name D symbol.val.name n _ found
  obtain ⟨sameProfile, sameSymbol⟩ :=
    relation_profile_unique symbol other named.symm
  subst profile
  have equal : symbol = other := eq_of_heq sameSymbol
  subst other
  exact found

/-- Lookup is defined for each declared function, at its actual declaration arity. -/
theorem function?_exists (D : Declarations) (declaration : TotalDeclaration)
    (member : declaration ∈ D.data.functions) :
    ∃ result : FunctionAt D declaration.inputs.length,
      function? D declaration.name declaration.inputs.length = some result := by
  cases found : function? D declaration.name declaration.inputs.length with
  | none =>
      unfold function? at found
      have missing := (List.findSome?_eq_none_iff.mp found)
        ⟨declaration, member⟩ (by simp)
      simp at missing
  | some result => exact ⟨result, rfl⟩

/-- Every declared function is found at its exact full profile. -/
theorem function?_complete {D : Declarations} {n : Nat} {w : Fin n → D.LocalSort} {s : D.LocalSort}
    (symbol : D.signature.Function n w s) :
    function? D symbol.val.name n = some ⟨w, s, symbol⟩ := by
  have arity : symbol.val.inputs.length = n := by
    rw [symbol.property.2.1, List.length_ofFn]
  have existsAt (k : Nat) (same : symbol.val.inputs.length = k) :
      ∃ result : FunctionAt D k, function? D symbol.val.name k = some result := by
    subst k
    exact function?_exists D symbol.val symbol.property.1
  obtain ⟨result, found⟩ := existsAt n arity
  rcases result with ⟨profile, output, other⟩
  have named := function?_name D symbol.val.name n _ found
  obtain ⟨sameProfile, sameOutput, sameSymbol⟩ :=
    function_profile_unique symbol other named.symm
  subst profile
  subst output
  have equal : symbol = other := eq_of_heq sameSymbol
  subst other
  exact found

/-- The dependent traversal succeeds when every ordered coordinate succeeds. -/
theorem sequence_complete (n : Nat) {β : Fin n → Type}
    (values : (i : Fin n) → β i) :
    sequence? n (fun i => some (values i)) = some values := by
  induction n with
  | zero =>
      simp only [sequence?]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      simp only [sequence?, ih, bind, Option.bind, Option.pure_def]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

/-- Erasing a typed local term is a complete inverse of the executable resolver.
No bound on depth or arity, or semantic carrier assumption, is used. -/
theorem eraseTerm_resolve {D : Declarations} (Γ : CheckedContext D) {s : D.LocalSort}
    (term : EQ.Term D.signature.toSignature Γ.profile s) :
    resolveTerm? Γ (eraseTerm Γ term) = some ⟨s, term⟩ := by
  refine EQ.Term.rec (motive := fun s term =>
    resolveTerm? Γ (eraseTerm Γ term) = some ⟨s, term⟩) ?_ ?_ term
  · intro i
    have lookup : (List.finRange Γ.bindings.length).find?
        (fun j => (Γ.bindings.get j).name == (Γ.bindings.get i).name) = some i := by
      cases found : (List.finRange Γ.bindings.length).find?
          (fun j => (Γ.bindings.get j).name == (Γ.bindings.get i).name) with
      | none =>
          have missing := (List.find?_eq_none.mp found) i (by simp)
          simp at missing
      | some j =>
          have named := List.find?_some found
          have equal : j = i := binding_name_injective Γ (by simpa using named)
          subst j
          rfl
    simp only [eraseTerm, resolveTerm?, lookup, bind, Option.bind, Option.pure_def]
  · intro n w s symbol arguments ih
    have children : (fun i => do
        let packed ← resolveTerm? Γ (eraseTerm Γ (arguments i))
        termAt? (w i) packed) = (fun i => some (arguments i)) := by
      funext i
      simp [ih i, termAt?]
    simp only [bind, Option.bind] at children
    simp only [eraseTerm, resolveTerm?, constructor?_complete, bind, Option.bind]
    rw [children, sequence_complete]
    rfl

/-- All equality, predicate and partial-row atoms survive canonical erasure
and resolution with their complete ordered typed arguments. -/
theorem eraseAtom_resolve {D : Declarations} (Γ : CheckedContext D)
    (atom : Core.Atom D.signature Γ.profile) :
    resolveAtom? Γ (eraseAtom Γ atom) = some atom := by
  have argumentsComplete : ∀ {n : Nat} {w : Fin n → D.LocalSort}
      (arguments : ∀ i, EQ.Term D.signature.toSignature Γ.profile (w i)),
      sequence? n (fun i => do
        let packed ← resolveTerm? Γ (eraseTerm Γ (arguments i))
        termAt? (w i) packed) = some arguments := by
    intro n w arguments
    have children : (fun i => do
        let packed ← resolveTerm? Γ (eraseTerm Γ (arguments i))
        termAt? (w i) packed) = (fun i => some (arguments i)) := by
      funext i
      simp [eraseTerm_resolve, termAt?]
    rw [children, sequence_complete]
  cases atom with
  | equal equality =>
      simp [eraseAtom, resolveAtom?, eraseTerm_resolve, termAt?]
  | relation predicate arguments =>
      simp only [eraseAtom, resolveAtom?, relation?_complete, bind, Option.bind]
      simp only [bind, Option.bind] at argumentsComplete
      rw [argumentsComplete]
      rfl
  | row function arguments value =>
      simp only [eraseAtom, resolveAtom?, function?_complete, bind, Option.bind]
      simp only [bind, Option.bind] at argumentsComplete
      rw [argumentsComplete]
      simp [eraseTerm_resolve, termAt?]

/-- Rechecking a legal complete context retains the exact original positions. -/
theorem CheckedContext.check_self {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name) :
    Context.check D Γ.bindings = some Γ := by
  have valid : Context.Valid D Γ.bindings := by
    refine ⟨Γ.unique, legal, ?_⟩
    intro binding member
    obtain ⟨index, equal⟩ := List.mem_iff_get.mp member
    rw [← equal]
    exact Γ.declared index
  unfold Context.check
  rw [dite_eq_left valid]

/-- Canonical atom lists retain every entry in its original order. -/
theorem eraseAtoms_resolve {D : Declarations} (Γ : CheckedContext D)
    (atoms : List (Core.Atom D.signature Γ.profile)) :
    (atoms.map (eraseAtom Γ)).mapM (resolveAtom? Γ) = some atoms := by
  induction atoms with
  | nil => rfl
  | cons first rest ih => simp [eraseAtom_resolve, ih]

/-- Canonical rule erasure retains the complete universal context. -/
theorem eraseRule_resolve {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (body : List (Core.Atom D.signature Γ.profile)) (head : Core.Atom D.signature Γ.profile) :
    resolveSentence? D (.rule Γ.bindings (body.map (eraseAtom Γ)) (eraseAtom Γ head)) =
      some (.rule ⟨Γ.bindings.length, Γ.profile, body, head⟩) := by
  simp only [resolveSentence?, Γ.check_self legal, bind, Option.bind,
    eraseAtoms_resolve, eraseAtom_resolve, Option.pure_def]

/-- Canonical query erasure retains the complete existential context. -/
theorem eraseQuery_resolve {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (goals : List (Core.Atom D.signature Γ.profile)) :
    resolveSentence? D (.query Γ.bindings (goals.map (eraseAtom Γ))) =
      some (.query ⟨Γ.bindings.length, Γ.profile, goals⟩) := by
  simp only [resolveSentence?, Γ.check_self legal, bind, Option.bind,
    eraseAtoms_resolve, Option.pure_def]

/-- The canonical full-file header contains all checked declarations. -/
def Declarations.header (D : Declarations) : List RawDeclaration :=
  D.data.sorts.map RawDeclaration.sort ++
    D.data.constructors.map RawDeclaration.constructor ++
    D.data.relations.map RawDeclaration.relation ++
    D.data.functions.map RawDeclaration.function

private def appendData (left right : DeclarationData) : DeclarationData :=
  ⟨left.sorts ++ right.sorts, left.constructors ++ right.constructors,
    left.relations ++ right.relations, left.functions ++ right.functions⟩

private theorem collect_append (left right : List RawDeclaration) :
    DeclarationData.collect (left ++ right) =
      appendData (DeclarationData.collect left) (DeclarationData.collect right) := by
  induction left with
  | nil => simp [DeclarationData.collect, appendData]
  | cons first rest ih =>
      cases first <;> simp [DeclarationData.collect, ih, appendData]

private theorem collect_sort_header (names : List String) :
    DeclarationData.collect (names.map RawDeclaration.sort) = ⟨names, [], [], []⟩ := by
  induction names <;> simp [DeclarationData.collect, *]

private theorem collect_constructor_header (entries : List TotalDeclaration) :
    DeclarationData.collect (entries.map RawDeclaration.constructor) = ⟨[], entries, [], []⟩ := by
  induction entries <;> simp [DeclarationData.collect, *]

private theorem collect_relation_header (entries : List RelationDeclaration) :
    DeclarationData.collect (entries.map RawDeclaration.relation) = ⟨[], [], entries, []⟩ := by
  induction entries <;> simp [DeclarationData.collect, *]

private theorem collect_function_header (entries : List TotalDeclaration) :
    DeclarationData.collect (entries.map RawDeclaration.function) = ⟨[], [], [], entries⟩ := by
  induction entries <;> simp [DeclarationData.collect, *]

theorem Declarations.collect_header (D : Declarations) :
    DeclarationData.collect D.header = D.data := by
  simp only [header, collect_append, collect_sort_header, collect_constructor_header,
    collect_relation_header, collect_function_header, appendData, List.nil_append,
    List.append_nil]

theorem Declarations.check_header (D : Declarations) :
    checkDeclarations D.header = some D := by
  unfold checkDeclarations
  rw [D.collect_header]
  unfold DeclarationData.check
  rw [dite_eq_left D.valid]

/-- Produce actual complete accepted bytes through the shared writer and reader.
The remaining lexical premise concerns the concrete encoded file only; it does
not assume a parser/resolver result or a naming view of the ambient signature. -/
def AcceptedUnit.canonical (D : Declarations) (raw : RawSentence)
    (resolved : Core.Sentence D.signature)
    (success : resolveSentence? D raw = some resolved)
    (legal : ∀ expression ∈ Parser.encodeProgram ⟨D.header, [raw]⟩,
      Smt.SExpr.Writer.LegalExpr expression) : AcceptedUnit where
  bytes := Parser.writeProgram ⟨D.header, [raw]⟩
  header := D.header
  declarations := D
  header_eq := D.check_header
  raw := raw
  read_eq := Parser.read_write_program _ legal
  resolved := resolved
  resolve_eq := success

local instance legalAtomDecidable (name : String) :
    Decidable (Smt.SExpr.Writer.LegalAtom name) := by
  unfold Smt.SExpr.Writer.LegalAtom Smt.SExpr.Writer.LegalChar
  infer_instance

/-- Canonical erased terms meet the actual shared writer's lexical contract. -/
theorem eraseTerm_legal {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name) {s : D.LocalSort}
    (term : EQ.Term D.signature.toSignature Γ.profile s) :
    Smt.SExpr.Writer.LegalExpr (Parser.encodeTerm (eraseTerm Γ term)) := by
  refine EQ.Term.rec (motive := fun _ term =>
    Smt.SExpr.Writer.LegalExpr (Parser.encodeTerm (eraseTerm Γ term))) ?_ ?_ term
  · intro i
    apply Smt.SExpr.Writer.LegalExpr.list
    intro expression member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .atom (by decide)
    · exact .atom (legal _ (List.get_mem _ _)).1
  · intro n w s symbol arguments ih
    apply Smt.SExpr.Writer.LegalExpr.list
    intro expression member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact .atom (by decide)
    · exact .atom ((D.valid.2.2.2.1 symbol.val
        (List.mem_append_left _ symbol.property.1)).1.1)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
      exact ih i

private theorem legal_argument_list {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name) {n : Nat}
    {w : Fin n → D.LocalSort}
    (arguments : ∀ i, EQ.Term D.signature.toSignature Γ.profile (w i)) :
    Smt.SExpr.Writer.LegalExpr
      (.list (List.ofFn (fun i => Parser.encodeTerm (eraseTerm Γ (arguments i))))) := by
  apply Smt.SExpr.Writer.LegalExpr.list
  intro expression member
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
  exact eraseTerm_legal Γ legal (arguments i)

/-- Every atom form has legal canonical bytes, including partial rows. -/
theorem eraseAtom_legal {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (atom : Core.Atom D.signature Γ.profile) :
    Smt.SExpr.Writer.LegalExpr (Parser.encodeAtom (eraseAtom Γ atom)) := by
  cases atom with
  | equal equality =>
      apply Smt.SExpr.Writer.LegalExpr.list
      intro expression member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact .atom (by decide)
      · exact eraseTerm_legal Γ legal equality.lhs
      · exact eraseTerm_legal Γ legal equality.rhs
  | relation predicate arguments =>
      apply Smt.SExpr.Writer.LegalExpr.list
      intro expression member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact .atom (by decide)
      · exact .atom ((D.valid.2.2.2.2 predicate.val predicate.property.1).1.1)
      · exact legal_argument_list Γ legal arguments
  | row function arguments value =>
      apply Smt.SExpr.Writer.LegalExpr.list
      intro expression member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact .atom (by decide)
      · exact .atom ((D.valid.2.2.2.1 function.val
          (List.mem_append_right _ function.property.1)).1.1)
      · exact legal_argument_list Γ legal arguments
      · exact eraseTerm_legal Γ legal value

private theorem legal_atoms (names : List String)
    (legal : ∀ name ∈ names, Smt.SExpr.Writer.LegalAtom name) :
    Smt.SExpr.Writer.LegalExpr (.list (names.map Smt.SE.atom)) := by
  apply Smt.SExpr.Writer.LegalExpr.list
  intro expression member
  obtain ⟨name, namedMember, rfl⟩ := List.mem_map.mp member
  exact .atom (legal name namedMember)

private theorem legal_total_declaration (tag : String) (entry : TotalDeclaration)
    (tagLegal : Smt.SExpr.Writer.LegalAtom tag)
    (nameLegal : Smt.SExpr.Writer.LegalAtom entry.name)
    (inputsLegal : ∀ name ∈ entry.inputs, Smt.SExpr.Writer.LegalAtom name)
    (outputLegal : Smt.SExpr.Writer.LegalAtom entry.output) :
    Smt.SExpr.Writer.LegalExpr (.list [.atom tag, .atom entry.name,
      .list (entry.inputs.map Smt.SE.atom), .atom entry.output]) := by
  apply Smt.SExpr.Writer.LegalExpr.list
  intro expression member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .atom tagLegal
  · exact .atom nameLegal
  · exact legal_atoms entry.inputs inputsLegal
  · exact .atom outputLegal

/-- Every declaration in the canonical full header is lexically accepted. -/
theorem Declarations.header_legal (D : Declarations) :
    ∀ expression ∈ D.header.map Parser.encodeDeclaration,
      Smt.SExpr.Writer.LegalExpr expression := by
  intro expression member
  obtain ⟨declaration, headerMember, rfl⟩ := List.mem_map.mp member
  simp only [header, List.mem_append, List.mem_map] at headerMember
  rcases headerMember with ((sort | constructor) | relation) | function
  · obtain ⟨name, sortMember, rfl⟩ := sort
    apply Smt.SExpr.Writer.LegalExpr.list
    intro expression member'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · exact .atom (by decide)
    · exact .atom (D.valid.2.2.1 name sortMember).1
  · obtain ⟨entry, constructorMember, rfl⟩ := constructor
    have valid := D.valid.2.2.2.1 entry (List.mem_append_left _ constructorMember)
    exact legal_total_declaration "constructor" entry (by decide) valid.1.1
      (fun name member => (D.valid.2.2.1 name (valid.2.1 name member)).1)
      (D.valid.2.2.1 entry.output valid.2.2).1
  · obtain ⟨entry, relationMember, rfl⟩ := relation
    have valid := D.valid.2.2.2.2 entry relationMember
    apply Smt.SExpr.Writer.LegalExpr.list
    intro expression member'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl | rfl
    · exact .atom (by decide)
    · exact .atom valid.1.1
    · exact legal_atoms entry.inputs
        (fun name member => (D.valid.2.2.1 name (valid.2 name member)).1)
  · obtain ⟨entry, functionMember, rfl⟩ := function
    have valid := D.valid.2.2.2.1 entry (List.mem_append_right _ functionMember)
    exact legal_total_declaration "function" entry (by decide) valid.1.1
      (fun name member => (D.valid.2.2.1 name (valid.2.1 name member)).1)
      (D.valid.2.2.1 entry.output valid.2.2).1

private theorem legal_context {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name) :
    Smt.SExpr.Writer.LegalExpr (.list (Γ.bindings.map Parser.encodeBinding)) := by
  apply Smt.SExpr.Writer.LegalExpr.list
  intro expression member
  obtain ⟨binding, bindingMember, rfl⟩ := List.mem_map.mp member
  have declared : binding.sort ∈ D.data.sorts := by
    obtain ⟨index, equal⟩ := List.mem_iff_get.mp bindingMember
    rw [← equal]
    exact Γ.declared index
  apply Smt.SExpr.Writer.LegalExpr.list
  intro expression member'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member'
  rcases member' with rfl | rfl
  · exact .atom (legal binding bindingMember).1
  · exact .atom (D.valid.2.2.1 binding.sort declared).1

private theorem legal_atom_list {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (atoms : List (Core.Atom D.signature Γ.profile)) :
    Smt.SExpr.Writer.LegalExpr
      (.list ((atoms.map (eraseAtom Γ)).map Parser.encodeAtom)) := by
  apply Smt.SExpr.Writer.LegalExpr.list
  intro expression member
  obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨atom, _, rfl⟩ := List.mem_map.mp rawMember
  exact eraseAtom_legal Γ legal atom

/-- Rules have canonical writer legality without an extra lexical assumption. -/
theorem eraseRule_legal {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (body : List (Core.Atom D.signature Γ.profile)) (head : Core.Atom D.signature Γ.profile) :
    Smt.SExpr.Writer.LegalExpr (Parser.encodeSentence
      (.rule Γ.bindings (body.map (eraseAtom Γ)) (eraseAtom Γ head))) := by
  apply Smt.SExpr.Writer.LegalExpr.list
  intro expression member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .atom (by decide)
  · exact legal_context Γ legal
  · exact legal_atom_list Γ legal body
  · exact eraseAtom_legal Γ legal head

/-- Queries have canonical writer legality with all unused binders retained. -/
theorem eraseQuery_legal {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (goals : List (Core.Atom D.signature Γ.profile)) :
    Smt.SExpr.Writer.LegalExpr (Parser.encodeSentence
      (.query Γ.bindings (goals.map (eraseAtom Γ)))) := by
  apply Smt.SExpr.Writer.LegalExpr.list
  intro expression member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .atom (by decide)
  · exact legal_context Γ legal
  · exact legal_atom_list Γ legal goals

theorem canonical_program_legal (D : Declarations) (raw : RawSentence)
    (legal : Smt.SExpr.Writer.LegalExpr (Parser.encodeSentence raw)) :
    ∀ expression ∈ Parser.encodeProgram ⟨D.header, [raw]⟩,
      Smt.SExpr.Writer.LegalExpr expression := by
  intro expression member
  simp only [Parser.encodeProgram, List.map_cons, List.map_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with header | rfl
  · exact D.header_legal expression header
  · exact legal

/-- Every rule over checked local declarations and a legal complete named
context has actual admitted complete bytes, with no parser/writer hypothesis. -/
def AcceptedUnit.canonicalRule {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (body : List (Core.Atom D.signature Γ.profile)) (head : Core.Atom D.signature Γ.profile) :
    AcceptedUnit :=
  canonical D (.rule Γ.bindings (body.map (eraseAtom Γ)) (eraseAtom Γ head))
    (.rule ⟨Γ.bindings.length, Γ.profile, body, head⟩)
    (eraseRule_resolve Γ legal body head)
    (canonical_program_legal D _ (eraseRule_legal Γ legal body head))

/-- Every query over the same full context has actual admitted complete bytes. -/
def AcceptedUnit.canonicalQuery {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (goals : List (Core.Atom D.signature Γ.profile)) : AcceptedUnit :=
  canonical D (.query Γ.bindings (goals.map (eraseAtom Γ)))
    (.query ⟨Γ.bindings.length, Γ.profile, goals⟩)
    (eraseQuery_resolve Γ legal goals)
    (canonical_program_legal D _ (eraseQuery_legal Γ legal goals))

theorem AcceptedUnit.canonicalRule_resolved {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (body : List (Core.Atom D.signature Γ.profile)) (head : Core.Atom D.signature Γ.profile) :
    (canonicalRule Γ legal body head).resolved =
      .rule ⟨Γ.bindings.length, Γ.profile, body, head⟩ := rfl

theorem AcceptedUnit.canonicalQuery_resolved {D : Declarations} (Γ : CheckedContext D)
    (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (goals : List (Core.Atom D.signature Γ.profile)) :
    (canonicalQuery Γ legal goals).resolved =
      .query ⟨Γ.bindings.length, Γ.profile, goals⟩ := rfl

/-- An unbounded executable supply of legal normalized identifiers. The length
encodes the index; no ambient enumeration or decimal lexer lemma is needed. -/
def finiteName (index : Nat) : String := String.ofList (List.replicate (index + 1) '_')

theorem finiteName_legal (index : Nat) : LegalName (finiteName index) := by
  have underscore : '_' ∈ (finiteName index).toList := by
    simp [finiteName]
  constructor
  · constructor
    · simp [finiteName]
    · intro character member
      have same : character = '_' := List.eq_of_mem_replicate
        (by simpa only [finiteName, String.toList_ofList] using member)
      subst character
      unfold Smt.SExpr.Writer.LegalChar
      decide
  · intro reserved
    have excluded : ∀ name ∈ ["sort", "constructor", "relation", "function", "rule", "query",
        "var", "app", "equal", "row"], '_' ∉ name.toList := by decide
    exact excluded _ reserved underscore

theorem finiteName_injective : Function.Injective finiteName := by
  intro left right same
  have lengths := congrArg (fun name : String => name.toList.length) same
  simpa [finiteName] using lengths

/-- Every finite typed context receives fresh legal names, including all unused
positions. This is independent of occurrence collection and carrier inhabitation. -/
def canonicalContext {D : Declarations} {n : Nat} (profile : Fin n → D.LocalSort) :
    CheckedContext D where
  bindings := List.ofFn (fun i => ⟨finiteName i.val, (profile i).val⟩)
  unique := by
    rw [List.map_ofFn]
    apply List.nodup_ofFn.mpr
    intro left right same
    exact Fin.ext (finiteName_injective same)
  declared := by
    intro index
    simpa only [List.get_ofFn] using
      (profile (Fin.cast (by simp) index)).property

theorem canonicalContext_legal {D : Declarations} {n : Nat}
    (profile : Fin n → D.LocalSort) :
    ∀ binding ∈ (canonicalContext profile).bindings, LegalName binding.name := by
  intro binding member
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact finiteName_legal index.val

/-- The canonical context is the identical complete typed tuple, modulo its
explicit length equality. In particular no unused or empty-sort binder is lost. -/
theorem canonicalContext_profile {D : Declarations} {n : Nat}
    (profile : Fin n → D.LocalSort) :
    (⟨(canonicalContext profile).bindings.length, (canonicalContext profile).profile⟩ :
      Σ arity, Fin arity → D.LocalSort) = ⟨n, profile⟩ := by
  apply Fin.sigma_eq_of_eq_comp_cast (by simp [canonicalContext])
  funext index
  apply Subtype.ext
  simp [canonicalContext, CheckedContext.profile]
  apply congrArg (fun i : Fin n => (profile i).val)
  exact Fin.ext rfl

/-- Exact local compilation, with declaration equality made explicit rather
than hidden inside a heterogeneous term or a semantic equivalence. -/
def AcceptedUnit.Realizes (unit : AcceptedUnit) (D : Declarations)
    (sentence : Core.Sentence D.signature) : Prop :=
  ∃ same : unit.declarations = D, same ▸ unit.resolved = sentence

theorem canonical_rule_at {D : Declarations} (tuple : Σ n, Fin n → D.LocalSort)
    (Γ : CheckedContext D) (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (same : (⟨Γ.bindings.length, Γ.profile⟩ : Σ n, Fin n → D.LocalSort) = tuple)
    (body : List (Core.Atom D.signature tuple.2)) (head : Core.Atom D.signature tuple.2) :
    ∃ unit : AcceptedUnit, unit.Realizes D (.rule ⟨tuple.1, tuple.2, body, head⟩) := by
  subst tuple
  exact ⟨AcceptedUnit.canonicalRule Γ legal body head, rfl, rfl⟩

theorem canonical_query_at {D : Declarations} (tuple : Σ n, Fin n → D.LocalSort)
    (Γ : CheckedContext D) (legal : ∀ binding ∈ Γ.bindings, LegalName binding.name)
    (same : (⟨Γ.bindings.length, Γ.profile⟩ : Σ n, Fin n → D.LocalSort) = tuple)
    (goals : List (Core.Atom D.signature tuple.2)) :
    ∃ unit : AcceptedUnit, unit.Realizes D (.query ⟨tuple.1, tuple.2, goals⟩) := by
  subst tuple
  exact ⟨AcceptedUnit.canonicalQuery Γ legal goals, rfl, rfl⟩

/-- Every Core sentence over arbitrary checked local declarations has actual
accepted complete bytes. Fresh binder names retain its full scope and profiles.
This is the local half of representation; arbitrary ambient finite support is
still a separate obligation, not an extra hypothesis on this theorem. -/
theorem localByteRepresentation (D : Declarations) (sentence : Core.Sentence D.signature) :
    ∃ unit : AcceptedUnit, unit.Realizes D sentence := by
  cases sentence with
  | rule rule =>
      exact canonical_rule_at ⟨rule.scope, rule.context⟩ (canonicalContext rule.context)
        (canonicalContext_legal rule.context) (canonicalContext_profile rule.context)
        rule.body rule.head
  | query query =>
      exact canonical_query_at ⟨query.scope, query.context⟩ (canonicalContext query.context)
        (canonicalContext_legal query.context) (canonicalContext_profile query.context)
        query.goals

/-- Exact map equality, rather than mere satisfaction equivalence, for the local
half of the final arbitrary-signature representation statement. -/
theorem localMappedRepresentation (D : Declarations) (sentence : Core.Sentence D.signature) :
    ∃ (unit : AcceptedUnit) (symbols : unit.declarations.signature ⟶ D.signature),
      unit.resolved.map symbols = sentence := by
  obtain ⟨unit, same, compiled⟩ := localByteRepresentation D sentence
  subst D
  exact ⟨unit, 𝟙 _, (Core.Sentence.map_id unit.resolved).trans compiled⟩

end Silmaril.Logic.Egglog.Source.Named
