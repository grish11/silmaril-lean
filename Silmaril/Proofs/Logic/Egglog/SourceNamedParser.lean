module

public import Silmaril.Logic.Egglog.Source.Named.Parser.Defs

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named.Parser
open Silmaril.Logic.Smt

private theorem nodes_le_nodesList {expression : SE} {expressions : List SE}
    (member : expression ∈ expressions) : nodes expression ≤ nodesList expressions := by
  induction expressions with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst first
        exact Nat.le_add_right _ _
      · exact le_trans (ih member) (Nat.le_add_left _ _)

private theorem mapM_map_some {α β : Type} (encode : α → β) (decode : β → Option α)
    (xs : List α) (roundtrip : ∀ x ∈ xs, decode (encode x) = some x) :
    (xs.map encode).mapM decode = some xs := by
  induction xs with
  | nil => rfl
  | cons first rest ih =>
      have hf := roundtrip first (by simp)
      have hr := ih (fun x member => roundtrip x (by simp [member]))
      simp [hf, hr]

/-- Every finite term receives enough executable fuel from its actual encoded
AST. The proof has no fixed nesting, arity or signature bound. -/
theorem term_encode_of_nodes_lt (raw : RawTerm) :
    ∀ fuel, nodes (encodeTerm raw) < fuel → term fuel (encodeTerm raw) = some raw := by
  exact RawTerm.rec
    (motive := fun raw => ∀ fuel, nodes (encodeTerm raw) < fuel →
      term fuel (encodeTerm raw) = some raw)
    (fun name fuel bound => by
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ bound)
      | succ fuel => rfl)
    (fun name n arguments ih fuel bound => by
      cases fuel with
      | zero => exact False.elim (Nat.not_lt_zero _ bound)
      | succ fuel =>
          have childBound (i : Fin n) : nodes (encodeTerm (arguments i)) < fuel := by
            have member : encodeTerm (arguments i) ∈
                List.ofFn (fun j : Fin n => encodeTerm (arguments j)) := by simp
            have le := nodes_le_nodesList member
            simp only [encodeTerm, nodes, nodesList] at bound
            omega
          have mapped := mapM_map_some encodeTerm (term fuel) (List.ofFn arguments)
            (fun argument member => by
              obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
              exact ih i fuel (childBound i))
          have mapped' : (List.ofFn (fun i : Fin n => encodeTerm (arguments i))).mapM
              (term fuel) = some (List.ofFn arguments) := by
            simpa only [List.map_ofFn, Function.comp_def] using mapped
          have rebuild : RawTerm.ofArgs name (List.ofFn arguments) =
              RawTerm.app name n arguments := by
            exact congrArg (fun tuple : Σ k, Fin k → RawTerm =>
              RawTerm.app name tuple.1 tuple.2)
              (List.equivSigmaTuple.apply_symm_apply ⟨n, arguments⟩)
          change Option.map (RawTerm.ofArgs name)
            ((List.ofFn (fun i : Fin n => encodeTerm (arguments i))).mapM (term fuel)) = _
          rw [mapped']
          exact congrArg some rebuild)
    raw

theorem term_roundtrip (raw : RawTerm) : term? (encodeTerm raw) = some raw :=
  term_encode_of_nodes_lt raw _ (Nat.lt_succ_self _)

private theorem tuple_rebuild {α β : Type} {n : Nat} (f : (n : Nat) → (Fin n → α) → β)
    (arguments : Fin n → α) :
    f (List.ofFn arguments).length (List.ofFn arguments).get = f n arguments :=
  congrArg (fun tuple : Σ k, Fin k → α => f tuple.1 tuple.2)
    (List.equivSigmaTuple.apply_symm_apply ⟨n, arguments⟩)

private theorem terms_roundtrip {n : Nat} (arguments : Fin n → RawTerm) :
    (List.ofFn (fun i => encodeTerm (arguments i))).mapM term? =
      some (List.ofFn arguments) := by
  simpa only [List.map_ofFn, Function.comp_def] using
    mapM_map_some encodeTerm term? (List.ofFn arguments) (fun raw _ => term_roundtrip raw)

theorem atom_roundtrip (raw : RawAtom) : atom (encodeAtom raw) = some raw := by
  cases raw with
  | equal left right => simp [encodeAtom, atom, term_roundtrip]
  | relation name n arguments =>
      change Option.bind
        ((List.ofFn (fun i => encodeTerm (arguments i))).mapM term?)
        (fun args => some (RawAtom.relation name args.length args.get)) = _
      rw [terms_roundtrip]
      exact congrArg some (tuple_rebuild (fun n args => RawAtom.relation name n args) arguments)
  | row name n arguments value =>
      change Option.bind
        ((List.ofFn (fun i => encodeTerm (arguments i))).mapM term?)
        (fun args => Option.bind (term? (encodeTerm value))
          (fun value => some (RawAtom.row name args.length args.get value))) = _
      rw [terms_roundtrip, term_roundtrip]
      exact congrArg some (tuple_rebuild (fun n args => RawAtom.row name n args value) arguments)

theorem sentence_roundtrip (raw : RawSentence) : sentence (encodeSentence raw) = some raw := by
  cases raw with
  | rule context body head =>
      have contextRoundtrip := mapM_map_some encodeBinding binding context (fun _ _ => rfl)
      have bodyRoundtrip := mapM_map_some encodeAtom atom body (fun raw _ => atom_roundtrip raw)
      simp [encodeSentence, sentence, contextRoundtrip, bodyRoundtrip, atom_roundtrip]
  | query context goals =>
      have contextRoundtrip := mapM_map_some encodeBinding binding context (fun _ _ => rfl)
      have goalsRoundtrip := mapM_map_some encodeAtom atom goals (fun raw _ => atom_roundtrip raw)
      simp [encodeSentence, sentence, contextRoundtrip, goalsRoundtrip]

theorem termRoundtrip_task : Task.termRoundtrip := term_roundtrip

theorem sentenceRoundtrip_task : Task.sentenceRoundtrip := sentence_roundtrip

theorem declaration_roundtrip (raw : RawDeclaration) :
    declaration (encodeDeclaration raw) = some raw := by
  have inputsRoundtrip (inputs : List String) :=
    mapM_map_some SE.atom sortName inputs (fun _ _ => rfl)
  cases raw with
  | sort name => rfl
  | constructor d => simp [encodeDeclaration, declaration, inputsRoundtrip]
  | relation d => simp [encodeDeclaration, declaration, inputsRoundtrip]
  | function d => simp [encodeDeclaration, declaration, inputsRoundtrip]

private theorem declaration_encodeSentence (raw : RawSentence) :
    declaration (encodeSentence raw) = none := by
  cases raw <;> rfl

private theorem program_encode (header : List RawDeclaration) (sentences : List RawSentence) :
    program (header.map encodeDeclaration ++ sentences.map encodeSentence) =
      some ⟨header, sentences⟩ := by
  induction header with
  | nil =>
      have mapped := mapM_map_some encodeSentence sentence sentences
        (fun raw _ => sentence_roundtrip raw)
      cases sentences with
      | nil => rfl
      | cons first rest =>
          simp only [List.map_nil, List.nil_append, List.map_cons, program,
            declaration_encodeSentence]
          simp only [List.map_cons] at mapped
          rw [mapped]
          rfl
  | cons first rest ih =>
      simp only [List.map_cons, List.cons_append, program, declaration_roundtrip]
      rw [ih]
      rfl

theorem program_roundtrip (raw : RawProgram) : program (encodeProgram raw) = some raw :=
  program_encode raw.declarations raw.sentences

theorem programRoundtrip_task : Task.programRoundtrip := program_roundtrip

/-- Actual canonical bytes re-enter through the complete shared ASCII reader.
The legal-atom premise is explicit; no parser oracle is assumed. -/
theorem read_write_program (raw : RawProgram)
    (legal : ∀ expression ∈ encodeProgram raw, SExpr.Writer.LegalExpr expression) :
    readProgram (writeProgram raw) = some raw := by
  unfold readProgram writeProgram
  rw [SExpr.Writer.read_renderForms _ legal]
  exact program_roundtrip raw

theorem read_write_sentence (raw : RawSentence)
    (legal : SExpr.Writer.LegalExpr (encodeSentence raw)) :
    readSentence (writeSentence raw) = some raw := by
  unfold readSentence writeSentence
  rw [SExpr.Writer.read_render _ legal]
  exact sentence_roundtrip raw

end Silmaril.Logic.Egglog.Source.Named.Parser
