module

public import Silmaril.Wasm.Logic.Kore.Operational.Conditional.Update.Source.Defs
import all Init.Data.String.Search
import all Init.Data.String.Slice.Numeric
import all Init.Data.String.Slice.Pattern
import all Init.Data.String.Basic
import all Init.Data.Int.Repr
import all Init.Data.Repr

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source

@[simp] theorem decode_encode (Γ : Context) (v : Valuation) : decode Γ (encode Γ v) = v := by
  cases v
  simp [decode, encode]

private theorem zero_read : ("0" : String).toInt? = some (0 : Int) := by cbv

private theorem intEquality_denote (Γ : Context) (ρ : Environment) :
    denote ρ (intEquality Γ) .boolean = some {intEqual (ρ .integer Γ.x) 0} := by
  simp [intEquality, denote, sortName, zero_read, image₂]

private theorem guardTree_denote (Γ : Context) (ρ : Environment) (g : Guard) :
    denote ρ (guardTree Γ g) .config = some { _c | g.Holds (ρ .integer Γ.x) } := by
  cases g <;> by_cases hx : ρ .integer Γ.x = 0 <;>
    simp [guardTree, denote, intEquality_denote, Guard.Holds, Guard.eval, intEqual, hx]

private theorem configTree_denote (Γ : Context) (ρ : Environment) (state : String) :
    denote ρ (configTree Γ state true) .config =
      some {c | ρ .integer Γ.x = ρ .valcell Γ.capturedVal ∧
        c = (⟨state :: ρ .code Γ.tail, ρ .integer Γ.x, ρ .counter Γ.counter⟩ : Config)} := by
  simp only [configTree, valueTree, denote, sortName, ↓reduceIte,
    Bind.bind, Option.bind, Pure.pure]
  ext c
  simp only [image₂]
  aesop

private theorem rhsTree_denote (Γ : Context) (ρ : Environment) (r : Rule)
    (read : LiteralReads r) :
    denote ρ (r.rhsTree Γ) .config = some {r.afterConfig (decode Γ ρ)} := by
  have parse : r.literal.repr.toInt? = some r.literal := read
  cases ht : r.target <;>
    simp [Rule.rhsTree, ht, denote, sortName, parse, image₂, Rule.afterConfig, decode]

theorem leftTree_denote (Γ : Context) (ρ : Environment) (r : Rule) :
    denote ρ (leftTree Γ r) .config = some {c |
      (decode Γ ρ).x = (decode Γ ρ).capturedVal ∧
      r.guard.Holds (decode Γ ρ).x ∧ c = r.beforeConfig (decode Γ ρ)} := by
  simp only [leftTree, denote, sortName, ne_eq, not_true_eq_false, ↓reduceIte,
    configTree_denote, guardTree_denote, Bind.bind, Option.bind, Pure.pure]
  congr 1
  ext c
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, decode, Rule.beforeConfig]
  tauto

theorem rightTree_denote (Γ : Context) (ρ : Environment) (r : Rule)
    (read : LiteralReads r) :
    denote ρ (rightTree Γ r) .config = some {r.afterConfig (decode Γ ρ)} := by
  simp [rightTree, denote, sortName, rhsTree_denote Γ ρ r read]

/-- Actual acceptance supplies the entire original tree and the literal reading;
there is no assumed semantic equation or validity premise. -/
theorem elaborate_shape {d : Declaration} {Γ : Context} {r : Rule}
    (accepted : elaborate d = some (Γ, r)) : d.body = r.tree Γ ∧ LiteralReads r := by
  unfold elaborate at accepted
  repeat' first
    | split at accepted
    | (dsimp only [Bind.bind, Option.bind, Pure.pure] at accepted; split at accepted)
  all_goals try simp only [Option.some.injEq, Prod.mk.injEq] at accepted
  all_goals rcases accepted with ⟨rfl, rfl⟩
  all_goals simp_all [LiteralReads, Rule.tree, Rule.rhsTree]

/-- Defined original source patterns have exactly the operational interpretation. -/
theorem elaborate_adequate {d : Declaration} {Γ : Context} {r : Rule}
    (accepted : elaborate d = some (Γ, r)) (ρ : Environment) :
    d.body = .rewrites "SortGeneratedTopCell" (leftTree Γ r) (rightTree Γ r) ∧
    denote ρ (leftTree Γ r) .config = some {c |
      (decode Γ ρ).x = (decode Γ ρ).capturedVal ∧
      r.guard.Holds (decode Γ ρ).x ∧ c = r.beforeConfig (decode Γ ρ)} ∧
    denote ρ (rightTree Γ r) .config = some {r.afterConfig (decode Γ ρ)} := by
  obtain ⟨shape, read⟩ := elaborate_shape accepted
  exact ⟨shape, leftTree_denote Γ ρ r, rightTree_denote Γ ρ r read⟩

/-- The original raw trees agree with the existing matching-pattern semantics,
including their definedness. The model relation is arbitrary. -/
theorem elaborate_to_matching {d : Declaration} {Γ : Context} {r : Rule}
    (accepted : elaborate d = some (Γ, r)) (ρ : Environment) (R : Config → Config → Prop) :
    ∃ lhs rhs, d.body = .rewrites "SortGeneratedTopCell" lhs rhs ∧
      denote ρ lhs .config = some ((model R).denote (valuation (decode Γ ρ)) r.pre) ∧
      denote ρ rhs .config = some ((model R).denote (valuation (decode Γ ρ)) r.post) := by
  obtain ⟨shape, left, right⟩ := elaborate_adequate accepted ρ
  refine ⟨leftTree Γ r, rightTree Γ r, shape, ?_, ?_⟩
  · rw [left]
    congr 1
    ext c
    rw [pre_mem]
    simp [valuation, environment_valuation]
  · rw [right, post_denote, environment_valuation]

/-- One independently interpreted source axiom yields its genuine update step. -/
theorem rawStep_of_elaborate {ds : List Declaration} {decl : Declaration}
    (member : decl ∈ ds) (isAxiom : decl.kind = .ruleAxiom) {Γ : Context} {r : Rule}
    (accepted : elaborate decl = some (Γ, r)) (v : Valuation)
    (coherent : v.x = v.capturedVal) (enabled : r.guard.Holds v.x) :
    RawStep ds (r.beforeConfig v) (r.afterConfig v) := by
  obtain ⟨shape, left, right⟩ := elaborate_adequate accepted (encode Γ v)
  refine ⟨decl, member, isAxiom, encode Γ v, leftTree Γ r, rightTree Γ r, _, _,
    shape, left, right, ?_, ?_⟩
  · simp only [decode_encode, Set.mem_ofPred_eq]
    exact ⟨coherent, enabled, trivial⟩
  · simp only [decode_encode, Set.mem_singleton_iff]

/-- Exact transition adequacy for original checked text. RawStep itself never
consults elaborate, the checked rule list, or synthesized pattern semantics. -/
theorem rawStep_iff_step {input : String} {p : CheckedProgram}
    (checked : check input = some p) (c d : Config) :
    RawStep p.declarations c d ↔ Step p.axioms c d := by
  constructor
  · rintro ⟨decl, member, isAxiom, ρ, lhs, rhs, left, right, body, hl, hr, hc, hd⟩
    obtain ⟨_, _, _, traversal⟩ := check_source checked
    have aligned := List.mapM_eq_some_iff_forall₂.mp traversal
    have every : ∀ (ds : List Declaration) (pairs : List (Context × Rule)),
        List.Forall₂ (fun d pair => elaborate d = some pair) ds pairs →
        ∀ decl ∈ ds, ∃ pair, elaborate decl = some pair := by
      intro ds pairs relation
      induction relation with
      | nil => simp
      | @cons decl pair ds pairs related _ ih =>
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨pair, related⟩
        · exact ih e he
    obtain ⟨⟨Γ, r⟩, accepted⟩ := every _ _ aligned decl member
    obtain ⟨shape, denLeft, denRight⟩ := elaborate_adequate accepted ρ
    have trees : lhs = leftTree Γ r ∧ rhs = rightTree Γ r := by
      exact Raw.rewrites.inj (body.symm.trans shape) |>.2
    rcases trees with ⟨rfl, rfl⟩
    have leftEq := Option.some.inj (hl.symm.trans denLeft)
    have rightEq := Option.some.inj (hr.symm.trans denRight)
    rw [leftEq] at hc
    rw [rightEq] at hd
    rcases hc with ⟨coherent, enabled, rfl⟩
    have installed : r ∈ p.axioms :=
      (axioms_iff checked r).2 ⟨decl, member, isAxiom, Γ, accepted,
        (checked_iff checked (Γ, r)).2 ⟨decl, member, accepted⟩⟩
    have target : d = r.afterConfig (decode Γ ρ) := hd
    subst d
    exact .rule r installed (decode Γ ρ) coherent enabled
  · intro step
    cases step with
    | rule r installed v coherent enabled =>
      obtain ⟨decl, member, isAxiom, Γ, accepted, _⟩ := (axioms_iff checked r).1 installed
      obtain ⟨shape, left, right⟩ := elaborate_adequate accepted (encode Γ v)
      refine ⟨decl, member, isAxiom, encode Γ v, leftTree Γ r, rightTree Γ r, _, _,
        shape, left, right, ?_, ?_⟩
      · simp only [decode_encode, Set.mem_ofPred_eq]
        exact ⟨coherent, enabled, trivial⟩
      · simp only [decode_encode, Set.mem_singleton_iff]

/-- Existing matching reachability soundness now holds in the independently
interpreted raw-source model, by the proved relation equality. -/
theorem raw_matching_sound {input : String} {p : CheckedProgram}
    (checked : check input = some p) (r : Rule) (installed : r ∈ p.axioms) :
    Matching.FixedPoint.Sentence.Satisfies (model (RawStep p.declarations))
      (Reachability.encode KSort.config r.compile) := by
  have relation : RawStep p.declarations = Step p.axioms := by
    funext c d
    exact propext (rawStep_iff_step checked c d)
  rw [relation]
  exact compiled_matching_sound p.axioms r installed

end Silmaril.Logic.Kore.Operational.Conditional.UpdateDraft.Source
