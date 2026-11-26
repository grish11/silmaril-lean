module

public import Silmaril.Proofs.SSA.PEG.Simple.While.Rows
public import Silmaril.Proofs.SSA.PEG.Simple.While.Trace

public section

namespace Silmaril.SSA.PEG.Simple.WhileProofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {out : Ty Data}
variable (p : WhileProgram P params out) (neg : P [.bool] .bool)
variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

private def clock (k : Nat) : Index 1 := fun _ => k

private theorem setClock (i : Index 1) (k : Nat) : i.set 0 k = clock k := by
  funext j
  have same : j = 0 := Fin.ext (by have := j.isLt; omega)
  subst j
  rfl

private def guardRef : Port p.layout .bool := p.localRef (p.core.refs.get .head)

private def exitRef : Port p.layout .bool := .tail (.tail .head)

variable (read : ∀ {t}, Port p.layout t → Index 1 → Option (m.Value t))

private def Carries (k : Nat) (store : Tuple m.Value params) : Prop :=
  ∀ t (slot : Port params t), read (p.carriedPort slot) (clock k) = some (store.get slot)

variable (eqs : ∀ (i : Index 1) t (r : Port p.layout t),
  read r i = rowValue m env (p.row neg r) read i)

include eqs

private theorem thetaEq {t : Ty Data} (slot : Port params t) (k : Nat) :
    read (p.carriedPort slot) (clock k) = rowValue m env (p.thetaRow slot) read (clock k) := by
  rw [eqs]
  unfold WhileProgram.carriedPort
  rw [localRow, liftedRow]

private theorem atEntry : Carries p m read 0 env := by
  intro t slot
  refine (thetaEq p neg m env read eqs slot 0).trans ?_
  change read (p.paramRef slot) (clock 0) = _
  rw [eqs, paramRow]
  rfl

private theorem thetaNext {t : Ty Data} (slot : Port params t) (k : Nat) :
    read (p.carriedPort slot) (clock (k + 1)) =
      read (p.localRef (p.core.refs.get (.tail slot))) (clock k) := by
  refine (thetaEq p neg m env read eqs slot (k + 1)).trans ?_
  change read (p.localRef (p.core.refs.get (.tail slot))) ((clock (k + 1)).set 0 k) = _
  rw [setClock]

private theorem evalCore {k : Nat} {store : Tuple m.Value params}
    (entry : Carries p m read k store) (t : Ty Data) (slot : Port p.core.nodes t) :
    read (p.localRef slot) (clock k) =
      (p.core.code.eval m env (store.map fun _ v => some v)).get slot := by
  apply closedEval m env p.core.code (p.thetaRow ·) (p.localRef ·) read (clock k)
  · intro t r
    rw [Proofs.get_map]
    exact entry t r
  · intro t r
    rw [eqs, localRow]

omit eqs in
private theorem seedRealizes (store : Tuple m.Value params) :
    Realizes m (store.map fun _ v => some v) (ports params) store := by
  intro t slot
  rw [Proofs.ports_get, Proofs.get_map]

private theorem guardAt {k : Nat} {store : Tuple m.Value params}
    (entry : Carries p m read k store) {b : Bool} (test : p.guard.eval m store = some ⟨b⟩) :
    read (guardRef p) (clock k) = some ⟨b⟩ := by
  unfold guardRef
  rw [evalCore p neg m env read eqs entry]
  let c := p.guard.lower (params := params) (ports params)
  let a := p.body.lower (params := params) (c.code.liftRefs (ports params))
  let seed := store.map fun _ v => some v
  change ((c.code.append a.code).eval m env seed).get (a.code.lift (c.refs.get .head)) = _
  rw [Proofs.eval_append, Proofs.eval_lift]
  exact Proofs.expr_correct m env p.guard (ports params) seed store (seedRealizes m store) test

private theorem bodyAt {k : Nat} {store next : Tuple m.Value params}
    (entry : Carries p m read k store) (run : Exec m p.body.enableWhile store (some next)) :
    Carries p m read (k + 1) next := by
  intro t slot
  change read (p.carriedPort slot) (clock (k + 1)) = _
  rw [thetaNext p neg m env read eqs, evalCore p neg m env read eqs entry]
  let c := p.guard.lower (params := params) (ports params)
  let a := p.body.lower (params := params) (c.code.liftRefs (ports params))
  let seed := store.map fun _ v => some v
  change ((c.code.append a.code).eval m env seed).get (a.refs.get slot) = _
  rw [Proofs.eval_append]
  have entryBody := Proofs.realizes_lift m env c.code (seedRealizes m store)
  exact Proofs.stmt_correct m env p.body (c.code.liftRefs (ports params)) _
    entryBody (forgetEnabled p.body run) t slot

omit eqs in
private theorem collectOne (collectRead : (j : Fin [Ty.bool].length) → Option (m.Value [Ty.bool][j])) :
    collect [.bool] collectRead = (collectRead 0).map (fun x => Tuple.cons x .nil) := by
  unfold collect
  cases collectRead 0 <;> rfl

private theorem exitAt
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {k : Nat} {store : Tuple m.Value params} (entry : Carries p m read k store)
    {b : Bool} (test : p.guard.eval m store = some ⟨b⟩) :
    read (exitRef p) (clock k) = some ⟨!b⟩ := by
  rw [eqs]
  change (collect (F := m.Value) [.bool] _).elim none (m.run neg) = _
  rw [collectOne]
  change ((read (guardRef p) (clock k)).map (fun x => .cons x .nil)).elim none (m.run neg) = _
  rw [guardAt p neg m env read eqs entry test]
  exact notSem b

private structure Reaches (i k : Nat) (final : Tuple m.Value params) : Prop where
  carries : Carries p m read (i + k) final
  exit : read (exitRef p) (clock (i + k)) = some ⟨true⟩
  earlier : ∀ j < k, read (exitRef p) (clock (i + j)) = some ⟨false⟩
  defined : ∀ j < k, ∀ t (slot : Port params t),
    (read (p.carriedPort slot) (clock (i + j))).isSome

private theorem traceCorrect
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {k : Nat} {store final : Tuple m.Value params}
    (run : WhileTrace m p.guard p.body.enableWhile k store final)
    (i : Nat) (entry : Carries p m read i store) : Reaches p m read i k final := by
  induction run generalizing i with
  | stop test =>
    refine ⟨entry, exitAt p neg m env read eqs notSem entry test, ?_, ?_⟩
    · intro j lt
      omega
    · intro j lt
      omega
  | @step k store next final test step rest ih =>
    have next := bodyAt p neg m env read eqs entry step
    have reached := ih (i + 1) next
    have offset (j : Nat) : i + (j + 1) = i + 1 + j := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [offset]
      exact reached.carries
    · rw [offset]
      exact reached.exit
    · intro j lt
      cases j with
      | zero => exact exitAt p neg m env read eqs notSem entry test
      | succ j =>
        rw [offset]
        exact reached.earlier j (by omega)
    · intro j lt t slot
      cases j with
      | zero =>
        have sample := entry t slot
        change read (p.carriedPort slot) (clock i) = _ at sample
        rw [Nat.add_zero, sample]
        rfl
      | succ j =>
        rw [offset]
        exact reached.defined j (by omega) t slot

omit eqs in
private theorem firstTrue_samples {flags : Nat → Option Bool} {k : Nat}
    (first : firstTrue flags = some k) :
    flags k = some true ∧ ∀ j < k, flags j = some false := by
  obtain ⟨hit, before⟩ := (firstTrue_eq_some_iff _ _).mp first
  obtain ⟨here, definedBefore⟩ := (monotonize_eq_some_iff _ _ _).mp hit
  refine ⟨here, fun j lt => ?_⟩
  have earlier := definedBefore j lt
  cases h : flags j with
  | none => simp [h] at earlier
  | some b =>
    cases b
    · rfl
    · exact (before j lt ((monotonize_eq_some_iff _ _ _).mpr
        ⟨h, fun t ht => definedBefore t (Nat.lt_trans ht lt)⟩)).elim

omit eqs in
theorem firstTrue_eq_some_iff_samples (flags : Nat → Option Bool) (k : Nat) :
    firstTrue flags = some k ↔ flags k = some true ∧ ∀ j < k, flags j = some false := by
  refine ⟨firstTrue_samples, fun ⟨stop, again⟩ => (firstTrue_eq_some_iff _ _).mpr ?_⟩
  refine ⟨(monotonize_eq_some_iff _ _ _).mpr ⟨stop, ?_⟩, ?_⟩
  · intro j hj
    rw [again j hj]
    rfl
  · intro j hj hit
    have atJ := ((monotonize_eq_some_iff _ _ _).mp hit).1
    rw [again j hj] at atJ
    cases atJ

private theorem passAt {k : Nat} {final : Tuple m.Value params}
    (reached : Reaches p m read 0 k final) (i : Index 1) :
    read p.passPort i = some ⟨k⟩ := by
  rw [eqs]
  change (firstTrue (fun j => (read (exitRef p) (i.set 0 j)).map ULift.down)).map ULift.up = _
  have stream (j : Nat) : (read (exitRef p) (i.set 0 j)).map ULift.down =
      (read (exitRef p) (clock j)).map ULift.down := by rw [setClock]
  simp only [stream]
  let flags := fun j => (read (exitRef p) (clock j)).map ULift.down
  have atExit : flags k = some true := by
    have sample := reached.exit
    change read (exitRef p) (clock (0 + k)) = _ at sample
    rw [Nat.zero_add] at sample
    unfold flags
    rw [sample]
    rfl
  have before (j : Nat) (lt : j < k) : flags j = some false := by
    have sample := reached.earlier j lt
    change read (exitRef p) (clock (0 + j)) = _ at sample
    rw [Nat.zero_add] at sample
    unfold flags
    rw [sample]
    rfl
  have first := (firstTrue_eq_some_iff_samples flags k).mpr ⟨atExit, before⟩
  change (firstTrue flags).map ULift.up = _
  rw [first]
  rfl

private theorem evalAt {k : Nat} {final : Tuple m.Value params}
    (reached : Reaches p m read 0 k final) (i : Index 1) :
    read (Port.head : Port p.layout out) i = some (final.get p.retvar) := by
  rw [eqs]
  change (read p.passPort i).elim none (fun count =>
    monotonize (fun j => read (p.carriedPort p.retvar) (i.set 0 j)) count.down) = _
  rw [passAt p neg m env read eqs reached i]
  change monotonize (fun j => read (p.carriedPort p.retvar) (i.set 0 j)) k = _
  apply (monotonize_eq_some_iff _ _ _).mpr
  constructor
  · rw [setClock]
    simpa only [Nat.zero_add] using reached.carries _ p.retvar
  · intro j lt
    rw [setClock]
    simpa only [Nat.zero_add] using reached.defined j lt _ p.retvar

omit eqs in
theorem returns
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {value : m.Value out} (run : p.source.Returns m env value)
    {values : (p.translate neg).Valuation m} (solves : (p.translate neg).Solves m env values)
    (i : Index 1) :
    (p.translate neg).observe m values i = .cons (some value) .nil := by
  obtain ⟨final, exec, returnValue⟩ := run
  obtain ⟨k, trace⟩ := whileTrace exec
  let read := fun {t} (slot : Port p.layout t) => p.readPort neg m values slot
  have eqs := fun i t slot => equationAt m env p neg solves i t slot
  have reached := traceCorrect p neg m env read eqs notSem trace 0 (atEntry p neg m env read eqs)
  have output := evalAt p neg m env read eqs reached i
  change Tuple.cons (F := fun t => Option (m.Value t)) (read Port.head i) .nil = _
  rw [output]
  change final.get p.retvar = value at returnValue
  rw [returnValue]

private theorem guardFromExit (total : p.Total m)
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {k : Nat} {store : Tuple m.Value params} (entry : Carries p m read k store) {b : Bool}
    (sample : (read (exitRef p) (clock k)).map ULift.down = some (!b)) :
    p.guard.eval m store = some ⟨b⟩ := by
  obtain ⟨actual, test⟩ := total.guard store
  rw [exitAt p neg m env read eqs notSem entry test] at sample
  cases actual <;> cases b <;> simp_all

private theorem traceFromPass (total : p.Total m)
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (i k : Nat) {store : Tuple m.Value params} (entry : Carries p m read i store)
    (stop : (read (exitRef p) (clock (i + k))).map ULift.down = some true)
    (again : ∀ j < k, (read (exitRef p) (clock (i + j))).map ULift.down = some false) :
    ∃ final, WhileTrace m p.guard p.body.enableWhile k store final ∧
      Carries p m read (i + k) final := by
  induction k generalizing i store with
  | zero =>
    have test := guardFromExit p neg m env read eqs total notSem entry (b := false)
      (by simpa using stop)
    exact ⟨store, .stop test, by simpa only [Nat.add_zero] using entry⟩
  | succ k ih =>
    have test := guardFromExit p neg m env read eqs total notSem entry (b := true)
      (by simpa using again 0 (Nat.zero_lt_succ _))
    obtain ⟨next, ran⟩ := total.body store
    have nextEntry := bodyAt p neg m env read eqs entry ran
    have offset (j : Nat) : i + 1 + j = i + (j + 1) := by omega
    obtain ⟨final, trace, carries⟩ := ih (i + 1) nextEntry
      (by rw [offset]; exact stop)
      (fun j hj => by rw [offset]; exact again (j + 1) (by omega))
    exact ⟨final, .step test ran trace, by rw [← offset]; exact carries⟩

omit eqs in
theorem exitWitness (total : p.Total m)
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {values : (p.translate neg).Valuation m} (solves : (p.translate neg).Solves m env values)
    (i : Index 1) {value : m.Value out}
    (defined : (p.translate neg).observe m values i = .cons (some value) .nil) :
    ∃ k final, p.ExitWitness neg m env values i k final value := by
  let read := fun {t} (slot : Port p.layout t) => p.readPort neg m values slot
  have eqs (i : Index 1) (t : Ty Data) (slot : Port p.layout t) :
      read slot i = rowValue m env (p.row neg slot) read i :=
    equationAt m env p neg solves i t slot
  have root : read (Port.head : Port p.layout out) i = some value :=
    congrArg (fun xs : Tuple (fun t => Option (m.Value t)) [out] => xs.get .head) defined
  rw [eqs i out (Port.head : Port p.layout out)] at root
  change (read p.passPort i).elim none (fun count =>
    monotonize (fun j => read (p.carriedPort p.retvar) (i.set 0 j)) count.down) = _ at root
  cases pass : read p.passPort i with
  | none => rw [pass] at root; cases root
  | some count =>
    rcases count with ⟨k⟩
    rw [pass] at root
    have evalSample : monotonize (fun j => read (p.carriedPort p.retvar) (clock j)) k =
        some value := by
      change monotonize (fun j => read (p.carriedPort p.retvar) (i.set 0 j)) k = some value at root
      simpa only [setClock] using root
    obtain ⟨sample, definedBefore⟩ := (monotonize_eq_some_iff _ _ _).mp evalSample
    let flags := fun j => (read (exitRef p) (clock j)).map ULift.down
    have passEq := eqs i .count p.passPort
    change read p.passPort i =
      (firstTrue (fun j => (read (exitRef p) (i.set 0 j)).map ULift.down)).map ULift.up at passEq
    simp only [setClock] at passEq
    change read p.passPort i = (firstTrue flags).map ULift.up at passEq
    rw [pass] at passEq
    have first : firstTrue flags = some k := by
      cases h : firstTrue flags with
      | none => rw [h] at passEq; cases passEq
      | some j =>
        rw [h] at passEq
        exact congrArg some (congrArg ULift.down (Option.some.inj passEq)).symm
    obtain ⟨stop, again⟩ := (firstTrue_eq_some_iff_samples flags k).mp first
    obtain ⟨final, trace, carries⟩ := traceFromPass p neg m env read eqs total notSem 0 k
      (atEntry p neg m env read eqs)
      (by simpa only [Nat.zero_add] using stop)
      (fun j hj => by simpa only [Nat.zero_add] using again j hj)
    have last : read (p.carriedPort p.retvar) (clock k) = some (final.get p.retvar) := by
      simpa only [Nat.zero_add] using carries _ p.retvar
    exact ⟨k, final, trace, Option.some.inj (last.symm.trans sample), pass, sample, definedBefore⟩

end Silmaril.SSA.PEG.Simple.WhileProofs
