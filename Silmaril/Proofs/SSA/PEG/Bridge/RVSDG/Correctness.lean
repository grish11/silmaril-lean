module

public import Silmaril.SSA.PEG.Bridge.RVSDG.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Proofs

open RVSDG (Port Tuple Origin Wires Locals)
open Compiler

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results ts : List (Ty Data)} {n k : Nat}
variable {g : Graph P params results n 0}

universe u

theorem collect_none {F : Ty Data → Type u} (ts : List (Ty Data))
    (read : ∀ s : Fin ts.length, Option (F ts[s])) (slot : Fin ts.length)
    (bottom : read slot = none) : collect ts read = none := by
  induction ts with
  | nil => exact slot.elim0
  | cons t ts ih =>
    refine Fin.cases (motive := fun s => read s = none → _) ?_ ?_ slot bottom
    · intro h
      simp [collect, h]
    · intro s h
      have missing := ih (fun i => read i.succ) s h
      cases first : read 0 <;> simp only [collect, missing, first]

private theorem collect_defined {F : Ty Data → Type} (xs : Tuple F ts) :
    collect ts (fun s => some (xs.get (portAt ts s))) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (match some x, collect _ (fun s => some (xs.get (portAt _ s))) with
      | some x, some ys => some (Tuple.cons x ys)
      | _, _ => none) = some (Tuple.cons x xs)
    rw [ih]

private def readOrigin {F : ValuePort Data → Type} {args : List (ValuePort Data)}
    {past : List (List (ValuePort Data))} (entry : Tuple F args) (locals : Locals F past)
    {t : ValuePort Data} (wire : Origin args past t) : F t :=
  (Wires.read (.cons wire .nil) entry locals).get .head

private theorem readOlder {F : ValuePort Data → Type}
    (past : List (List (ValuePort Data))) {head : List (ValuePort Data)}
    (locals : Locals F past) (output : Tuple F head) (j : Fin past.length)
    {t : ValuePort Data} (p : Port past[j] t) :
    ((locals.snoc output).get ⟨j.val, by simp; omega⟩).get
      ((List.getElem_append_left j.isLt).symm ▸ p) = (locals.get j).get p := by
  induction past with
  | nil => exact j.elim0
  | cons a past ih =>
    refine Fin.cases (motive := fun j => ∀ p : Port (a :: past)[j] t,
      ((locals.snoc output).get ⟨j.val, by simp; omega⟩).get
        ((List.getElem_append_left (as := a :: past) j.isLt).symm ▸ p) =
          (locals.get j).get p) ?_ ?_ j p
    · intro p
      rfl
    · intro j p
      exact ih locals.2 j p

private theorem readNew {F : ValuePort Data → Type} {args : List (ValuePort Data)}
    (entry : Tuple F args) (past : List (List (ValuePort Data))) (locals : Locals F past)
    {t : Ty Data} (v : F (.value t)) :
    readOrigin entry (locals.snoc (.cons v .nil)) (newest past t) = v := by
  induction past with
  | nil => rfl
  | cons a past ih => exact ih locals.2

private theorem readWeaken {F : ValuePort Data → Type} {args : List (ValuePort Data)}
    {past : List (List (ValuePort Data))} {head : List (ValuePort Data)}
    (entry : Tuple F args) (locals : Locals F past) (output : Tuple F head)
    {t : ValuePort Data} (wire : Origin args past t) :
    readOrigin entry (locals.snoc output) (weaken head wire) = readOrigin entry locals wire := by
  cases wire with
  | arg => rfl
  | output j p => exact readOlder past locals output j p

private theorem readValuePort {F : ValuePort Data → Type}
    (xs : Tuple (fun t => F (.value t)) ts) {t : Ty Data} (p : Port ts t) :
    (toPorts (F := F) xs).get (portToValue p) = xs.get p := by
  induction p with
  | head => cases xs; rfl
  | tail p ih => cases xs; exact ih _

theorem from_toPorts {F : ValuePort Data → Type} (xs : Tuple (fun t => F (.value t)) ts) :
    fromPorts ts (toPorts (F := F) xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [toPorts, fromPorts, ih]

theorem to_fromPorts {F : ValuePort Data → Type} (xs : Tuple F (valuePorts ts)) :
    toPorts (fromPorts ts xs) = xs := by
  induction ts with
  | nil => cases xs; rfl
  | cons t ts ih => cases xs; simp [toPorts, fromPorts, ih]

variable (m : TotalModel P) (env : Tuple m.toPEG.Value params) (idx : Index 0)

private abbrev DefinedScope {past : List (List (ValuePort Data))}
    (scope : Scope g k past) (locals : Locals m.toRVSDG.Val past) (values : g.Valuation m.toPEG) :=
  ∀ j hj, values (j, idx) = some (readOrigin (toPorts (F := m.toRVSDG.Val) env) locals (scope j hj))

private theorem readResolved {past : List (List (ValuePort Data))}
    (scope : Scope g k past) (locals : Locals m.toRVSDG.Val past) (values : g.Valuation m.toPEG)
    (agree : DefinedScope m env idx scope locals values)
    {t : Ty Data} (r : Ref g.sort t) (bound : r.id.val < k) :
    r.read m.carrier (values (r.id, idx)) =
      some (readOrigin (toPorts (F := m.toRVSDG.Val) env) locals (resolve scope r bound)) := by
  rw [agree r.id bound]
  obtain ⟨j, typed⟩ := r
  cases typed
  rfl

private theorem wireRefs_read {past : List (List (ValuePort Data))}
    (scope : Scope g k past) (locals : Locals m.toRVSDG.Val past) (rs : Tuple (Ref g.sort) ts)
    (bound : ∀ s : Fin ts.length, (rs.get (portAt ts s)).id.val < k) (s : Fin ts.length) :
    (fromPorts ts ((wireRefs scope rs bound).read (toPorts (F := m.toRVSDG.Val) env) locals)).get
        (portAt ts s) =
      readOrigin (toPorts (F := m.toRVSDG.Val) env) locals
        (resolve scope (rs.get (portAt ts s)) (bound s)) := by
  induction rs with
  | nil => exact s.elim0
  | cons r rs ih =>
    revert s
    refine Fin.cases ?_ ?_
    · rfl
    · intro j
      exact ih (fun i => bound i.succ) j

private theorem roots_read {past : List (List (ValuePort Data))}
    (scope : Scope g k past) (locals : Locals m.toRVSDG.Val past) (values : g.Valuation m.toPEG)
    (agree : DefinedScope m env idx scope locals values) (rs : Tuple (Ref g.sort) ts)
    (bound : ∀ s : Fin ts.length, (rs.get (portAt ts s)).id.val < k) :
    rs.map (fun _ r => r.read m.carrier (values (r.id, idx))) =
      (fromPorts ts ((wireRefs scope rs bound).read (toPorts (F := m.toRVSDG.Val) env) locals)).map
        (fun _ => some) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have head := readResolved m env idx scope locals values agree r (bound 0)
    exact congrArg₂ Tuple.cons head (ih (fun i => bound i.succ))

private theorem label_correct {ins : List (Ty Data)} {out : Ty Data}
    (label : Label P params (Fin 0) ins out) {past : List (List (ValuePort Data))}
    (wires : Wires (valuePorts params) past (valuePorts ins)) (locals : Locals m.toRVSDG.Val past)
    (read : ∀ (s : Fin ins.length) (j : Index 0),
      (label.kind s).Changes idx j → Option (m.toPEG.Value ins[s]))
    (defined : ∀ s h, read s idx h =
      some ((fromPorts ins (wires.read (toPorts (F := m.toRVSDG.Val) env) locals)).get (portAt ins s))) :
    let op := lowerLabel label wires
    let v := op.2.1.eval m (fromPorts op.1 (op.2.2.read (toPorts (F := m.toRVSDG.Val) env) locals))
    label.interpret m.toPEG env idx read = some v := by
  cases label with
  | param slot =>
    change some (env.get slot) = some ((toPorts (F := m.toRVSDG.Val) env).get (portToValue slot))
    exact congrArg some (readValuePort (F := m.toRVSDG.Val) env slot).symm
  | op op =>
    let args : Tuple m.toPEG.Value ins := fromPorts ins (wires.read (toPorts (F := m.toRVSDG.Val) env) locals)
    have all : (fun s => read s idx rfl) = (fun s => some (args.get (portAt ins s))) :=
      funext (fun s => defined s rfl)
    change (collect ins (fun s => read s idx rfl)).elim none (fun xs => some (m.run op xs)) =
      some (m.run op args)
    rw [all, collect_defined (F := m.toPEG.Value) args]
    rfl
  | phi =>
    change (read 0 idx rfl).elim none (fun flag => if flag.down then read 1 idx rfl else read 2 idx rfl)
      = some (Operation.eval m (.select (out := out))
        (fromPorts _ (wires.read (toPorts (F := m.toRVSDG.Val) env) locals)))
    rw [defined 0 rfl, defined 1 rfl, defined 2 rfl]
    generalize fromPorts _ (wires.read (toPorts (F := m.toRVSDG.Val) env) locals) = xs
    cases xs with
    | cons flag xs => cases xs with
      | cons left xs => cases xs with
        | cons right xs =>
          cases xs
          change (if flag.down then some left else some right) = some (if flag.down then left else right)
          split <;> rfl
  | theta l | eval l | pass l => exact l.elim0

private theorem push_agrees {past : List (List (ValuePort Data))}
    (scope : Scope g k past) (locals : Locals m.toRVSDG.Val past) (values : g.Valuation m.toPEG)
    (agree : DefinedScope m env idx scope locals values) (i : Fin n) (cursor : i.val = k)
    (out : m.toPEG.Value (g.sort i)) (current : values (i, idx) = some out) :
    DefinedScope m env idx (scope.push i cursor) (locals.snoc (.cons out .nil)) values := by
  intro j hj
  by_cases old : j.val < k
  · rw [show scope.push i cursor j hj = weaken _ (scope j old) by simp [Scope.push, old]]
    rw [readWeaken]
    exact agree j old
  · have eq : j = i := Fin.ext (by omega)
    subst j
    rw [show scope.push i cursor i hj = newest past (g.sort i) by simp [Scope.push, old]]
    exact current.trans (congrArg some
      (readNew (toPorts (F := m.toRVSDG.Val) env) past locals out).symm)

private theorem compile_correct (g : Graph P params results n 0) (ordered : Ordered g)
    (values : g.Valuation m.toPEG) (solves : g.Solves m.toPEG env values)
    (remaining k : Nat) (size : k + remaining = n) {past : List (List (ValuePort Data))}
    (scope : Scope g k past) (locals : Locals m.toRVSDG.Val past)
    (agree : DefinedScope m env idx scope locals values) :
    g.observe m.toPEG values idx =
      (fromPorts results ((compileFrom g ordered remaining k size scope).2.eval
        m.toRVSDG (toPorts (F := m.toRVSDG.Val) env) locals)).map (fun _ => some) := by
  induction remaining generalizing k past with
  | zero =>
    rw [compileFrom]
    exact roots_read m env idx scope locals values agree g.roots _
  | succ remaining ih =>
    rw [compileFrom]
    let i : Fin n := ⟨k, by omega⟩
    let source := g.node i
    let wires := wireRefs scope source.args (ordered i)
    let op := lowerLabel source.label wires
    let output := op.2.1.eval m (fromPorts op.1 (op.2.2.read (toPorts (F := m.toRVSDG.Val) env) locals))
    have current : values (i, idx) = some output := by
      rw [solves (i, idx)]
      exact label_correct m env idx source.label wires locals
        (fun s j _ => (source.arg s).read m.carrier (values ((source.arg s).id, j)))
        (fun s _ => (readResolved m env idx scope locals values agree (source.arg s)
          (ordered i s)).trans (congrArg some (wireRefs_read m env scope locals source.args
            (ordered i) s).symm))
    change _ = (fromPorts results ((compileFrom g ordered remaining (k + 1) _ (scope.push i rfl)).2.eval
      m.toRVSDG (toPorts (F := m.toRVSDG.Val) env) (locals.snoc (head := valuePorts [g.sort i]) (.cons output .nil)))).map (fun _ => some)
    exact ih (k + 1) _ (scope.push i rfl) _ (push_agrees m env idx scope locals values agree i rfl
      output current)

theorem translate_correct (g : Graph P params results n 0) (ordered : Ordered g)
    (wf : WellFounded g.Demand) :
    g.observe m.toPEG (g.denote m.toPEG env wf) idx =
      (fromPorts results ((translate g ordered).2.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env))).map (fun _ => some) := by
  unfold translate
  rw [RVSDG.Term.run_toGraph]
  exact compile_correct m env idx g ordered _ (g.denote_solves m.toPEG env wf) n 0
    (Nat.zero_add _) (past := []) _ PUnit.unit (fun _ h => by omega)

end Silmaril.SSA.PEG.Bridge.Proofs
