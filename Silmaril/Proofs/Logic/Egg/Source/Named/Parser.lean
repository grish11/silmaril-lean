module

public import Silmaril.Logic.Egg.Source.Named.Parser.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named.Parser
open Silmaril.Logic.Smt
open Silmaril.Logic.Egglog.Source.Named.Parser (nodes nodesList)

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
    (fun name result n arguments ih fuel bound => by
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
          have rebuild : RawTerm.ofArgs name result (List.ofFn arguments) =
              RawTerm.app name result n arguments := by
            exact congrArg (fun tuple : Σ k, Fin k → RawTerm =>
              RawTerm.app name result tuple.1 tuple.2)
              (List.equivSigmaTuple.apply_symm_apply ⟨n, arguments⟩)
          change Option.map (RawTerm.ofArgs name result)
            ((List.ofFn (fun i : Fin n => encodeTerm (arguments i))).mapM (term fuel)) = _
          rw [mapped']
          exact congrArg some rebuild)
    raw

theorem term_roundtrip (raw : RawTerm) : term? (encodeTerm raw) = some raw :=
  term_encode_of_nodes_lt raw _ (Nat.lt_succ_self _)

theorem equality_roundtrip (e : RawEquality) : equality (encodeEquality e) = some e := by
  cases e
  simp [encodeEquality, equality, term_roundtrip]

theorem rule_roundtrip (r : RawRule) : rule (encodeRule r) = some r := by
  rcases r with ⟨name, context, guards, conclusion⟩
  have contextRoundtrip := mapM_map_some
    (fun b : Silmaril.Logic.Egglog.Source.Named.Binding =>
      SE.list [SE.atom b.name, SE.atom b.sort])
    Silmaril.Logic.Egglog.Source.Named.Parser.binding context (fun _ _ => rfl)
  have guardRoundtrip := mapM_map_some encodeEquality equality guards
    (fun e _ => equality_roundtrip e)
  simp [encodeRule, rule, contextRoundtrip, guardRoundtrip, equality_roundtrip]

/-- Concrete bytes use the same complete reader as all supplied/inferred
admission paths. The premise only concerns the actual lexical atom syntax. -/
def writeProgram (p : RawProgram) : List UInt8 :=
  SExpr.Writer.renderForms (p.map encodeRule)

theorem read_write_program (p : RawProgram)
    (legal : ∀ e ∈ p.map encodeRule, SExpr.Writer.LegalExpr e) :
    readProgram (writeProgram p) = some p := by
  unfold readProgram writeProgram
  rw [SExpr.Writer.read_renderForms _ legal]
  exact mapM_map_some encodeRule rule p (fun r _ => rule_roundtrip r)

end Silmaril.Logic.Egg.Source.Named.Parser
