module

public import Silmaril.Machine.Vex.Validate.Defs

public section

namespace Silmaril.Machine.Vex.Proofs

open AMD64Scalar

theorem boundaryBeh {input output : Type} (run : input → output) (entry : input)
    (outcome : Behaviour.Outcome output Empty Empty) :
    (boundarySem run).Beh entry outcome ↔ outcome = .returned (run entry) := by
  rw [Behaviour.Semantics.beh_of_stop (fun _ h => h)]
  change (outcome = .returned (run entry) ∧ outcome ≠ .diverges) ↔ _
  constructor
  · exact And.left
  · rintro rfl
    exact ⟨rfl, by simp⟩

theorem boundaryRefines {srcInit tgtInit observation : Type}
    (source : srcInit → observation) (target : tgtInit → observation)
    (initial : srcInit → tgtInit → Prop)
    (agree : ∀ src tgt, initial src tgt → source src = target tgt) :
    Behaviour.Refines .strict (boundarySem target) (boundarySem source)
      (fun tgt src => initial src tgt) (fun _ _ => Behaviour.Obs.id) := by
  intro tgt src related _ outcome behavior
  refine ⟨.returned (source src), (boundaryBeh source src _).mpr rfl, ?_⟩
  rw [Behaviour.Outcome.Rel.strict_id_iff, (boundaryBeh target tgt _).mp behavior, agree src tgt related]

private theorem flagBit (value : Bool) : (flagWord value).getLsbD 0 = value := by
  cases value <;> decide

theorem selectBit (input : Input) (index : Nat) (term : Term) :
    (term.selectBit index).eval input = flagWord ((term.eval input).getLsbD index) := by
  cases term with
  | eq lhs rhs =>
    change (if index = 0 then Term.eq lhs rhs else .bit index (.eq lhs rhs)).eval input = _
    by_cases equal : index = 0
    · subst index
      rw [ite_eq_left rfl]
      exact congrArg flagWord (flagBit (lhs.eval input == rhs.eval input)).symm
    · rw [ite_eq_right equal]; rfl
  | initialZF =>
    change (if index = 0 then Term.initialZF else .bit index .initialZF).eval input = _
    by_cases equal : index = 0
    · subst index
      rw [ite_eq_left rfl]
      exact congrArg flagWord (flagBit input.zf).symm
    · rw [ite_eq_right equal]; rfl
  | initialFlags =>
    change (if index = 6 then Term.initialZF else .bit index .initialFlags).eval input = _
    by_cases equal : index = 6
    · subst index
      rw [ite_eq_left rfl]
      change flagWord input.zf = flagWord ((if input.zf then (64 : Word) else 0).getLsbD 6)
      generalize input.zf = value
      cases value <;> decide
    · rw [ite_eq_right equal]; rfl
  | const | reg | add | bit => rfl

private def evaluate (input : Input) (state : State Term Term) : Input :=
  ⟨state.rax.eval input, state.rdi.eval input, state.rsi.eval input, state.zf.test input, state.rip⟩

private theorem testEq (input : Input) (lhs rhs : Term) :
    (Term.eq lhs rhs).test input = (lhs.eval input == rhs.eval input) := by
  exact flagBit (lhs.eval input == rhs.eval input)

private theorem evaluateStep (input : Input) (state : State Term Term) (op : X86.Op) :
    evaluate input (op.step X86.symbolic state) = op.step X86.concrete (evaluate input state) := by
  cases op <;> simp [X86.Op.step, X86.symbolic, X86.concrete, evaluate, testEq, Term.eval]

private theorem evaluateBody (input : Input) (state : State Term Term) (body : List X86.Op) :
    evaluate input (body.foldl (X86.Op.step X86.symbolic) state) =
    body.foldl (X86.Op.step X86.concrete) (evaluate input state) := by
  induction body generalizing state with
  | nil => rfl
  | cons op rest ih => simp only [List.foldl_cons, ih, evaluateStep]

private theorem evaluateExit (input : Input) (zf : Term) (exit : X86.Exit) :
    (exit.next zf).map (Term.test input) = exit.next (zf.test input) := by
  cases exit with
  | jmp => rfl
  | jcc zero => cases zero <;> rfl

private theorem evaluateEntry (input : Input) : evaluate input (X86.entry input.rip) = input := by
  cases input with
  | mk rax rdi rsi zf rip => cases zf <;> simp [evaluate, X86.entry, Term.eval, Term.test, flagWord, State.read]

private theorem evaluatePlan (input : Input) (state : State Term Term) (exit : X86.Exit) :
    (Plan.mk state.rax state.rdi state.rsi state.zf (exit.next state.zf)).eval input =
      { evaluate input state with rip := (exit.next (evaluate input state).zf).target } := by
  simp [Plan.eval, evaluateExit, evaluate]

theorem x86Lower (block : X86.Block) (input : Input) :
    (block.lower input.rip).eval input = block.run input := by
  unfold X86.Block.lower X86.Block.run
  rw [evaluatePlan, evaluateBody, evaluateEntry]

theorem artifacts {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) :
    X86.decode pc bytes = .ok pair.source ∧ check raw = .ok pair.target ∧
    pair.target.address = pc ∧ pair.target.code.marks = pair.source.marks ∧
    pair.target.lower = .ok (pair.source.lower pc) := by
  cases hd : X86.decode pc bytes with
  | error => simp [validate, hd] at accepted
  | ok source =>
    cases hc : check raw with
    | error => simp [validate, hd, hc] at accepted
    | ok target =>
      by_cases ha : target.address = pc
      · by_cases hm : source.marks = target.code.marks
        · cases hl : target.lower with
          | error => simp [validate, hd, hc, ha, hm, hl] at accepted
          | ok plan =>
            by_cases hp : source.lower pc = plan
            · simp [validate, hd, hc, ha, hm, hl, hp] at accepted
              cases accepted
              exact ⟨rfl, rfl, ha, hm.symm, by simpa only [hp] using hl⟩
            · simp [validate, hd, hc, ha, hm, hl, hp] at accepted
        · simp [validate, hd, hc, ha, hm] at accepted
      · simp [validate, hd, hc, ha] at accepted

theorem validateSound {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) (input : Input) (entry : input.rip = pc) :
    pair.target.run input = .ok (pair.source.run input) := by
  simp only [Block.run, (artifacts accepted).2.2.2.2, Except.map, ← entry, x86Lower]

theorem validateBoundary {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) :
    BoundaryAgreement pair.source.run pair.target.run (Initial pc) Final
      (fun state => some (observe state)) (fun result => result.toOption.map observe) := by
  rintro input _ ⟨rfl, entry⟩
  rw [validateSound accepted input entry]
  exact ⟨⟨_, rfl, rfl⟩, rfl⟩

theorem validateRefines {pc : Word} {bytes : List UInt8} {raw : Raw.Block} {pair : Pair}
    (accepted : validate pc bytes raw = .ok pair) :
    ∃ plan, pair.target.lower = .ok plan ∧
      Behaviour.Refines .strict (boundarySem (fun input => plan.eval input))
        (boundarySem pair.source.run) (fun tgt src => Initial pc src tgt)
        (fun _ _ => Behaviour.Obs.id) := by
  refine ⟨_, (artifacts accepted).2.2.2.2, boundaryRefines _ _ (Initial pc) ?_⟩
  rintro input _ ⟨rfl, entry⟩
  exact (entry ▸ x86Lower pair.source input).symm

theorem wordErasure {ctx : Scope} (value : Word) :
    checkExpr ctx ((Expr.word (ctx := ctx) value).erase) = .ok ⟨.i64, Expr.word value⟩ := by
  have checked : checkWord value.toNat = .ok value := by simp [checkWord, value.isLt]
  let wrap (result : Word) : Except Error (Σ ty, Expr ctx ty) := .ok ⟨.i64, .word result⟩
  change (checkWord value.toNat >>= wrap) = _
  rw [checked]
  rfl

end Silmaril.Machine.Vex.Proofs
