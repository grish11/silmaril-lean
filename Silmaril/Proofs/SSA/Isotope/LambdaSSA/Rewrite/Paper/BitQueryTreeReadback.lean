module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Default.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms

/-! # Native certificates for the finite Bit request readback -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeReadback

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.RequestTree
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (Live slots literalQuery readQuery forwarding enter? Candidate Direct QueryMode Decision readDecision readDecision_eq)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Assignment)

private theorem slots_ext {Γ : List (Ty Empty)} {n : Nat} {a b : Slots Γ n}
    (h : a.index = b.index) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem nextSlot (n : Nat) : (slots n).bind = slots (n + 1) :=
  slots_ext (funext fun i => Fin.cases rfl (fun _ => rfl) i)

private theorem labelShift (pre : List (Ty Empty)) :
    Ren Exits (pre ++ Exits) (pre.length + ·) := by
  intro i A hi
  simpa [At, List.getElem?_append_right (Nat.le_add_right _ _)] using hi

private theorem requestType {Γ : List (Ty Empty)} {label : Bool} {arg : Tm signature.Instr}
    {A B : Ty Empty} (ha : Tm.HasType Γ (.op (.ask label) arg) (Ty.coprod A B)) :
    A = Bit ∧ B = Bit := by
  cases ha
  exact ⟨rfl, rfl⟩

private theorem literalQuery_eq {a : Tm signature.Instr} {b : Bool} (h : literalQuery a = some b) :
    a = literal b := by
  fun_cases literalQuery a <;> simp_all [literalQuery, literal, constructorBit]

private theorem readQuery_spec {written : Bool} {n : Nat} {a : Tm signature.Instr} {e : Expr n}
    (h : readQuery written n a = some e) :
    (∃ b, e = .literal b ∧ a = literal b) ∨
      (written = true ∧ ∃ i, e = .read i ∧ a = (slots n).terms i) := by
  fun_cases readQuery written n a
  · rename_i within
    rw [readQuery, dite_eq_left within] at h
    cases h
    exact .inr ⟨within.1, _, rfl, rfl⟩
  · rename_i outside
    simp [readQuery, outside] at h
  · rename_i notVar
    have found : (literalQuery a).map Expr.literal = some e := by
      cases a <;> simp_all [readQuery]
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp found
    exact .inl ⟨b, rfl, literalQuery_eq hb⟩

theorem readQuery_typed {written : Bool} {n : Nat} {arg : Tm signature.Instr} {query : Expr n}
    (h : readQuery written n arg = some query) : Tm.HasType (Live n) arg Bit := by
  rcases readQuery_spec h with ⟨b, _, rfl⟩ | ⟨_, i, _, rfl⟩
  · exact (constructorBit_value b .unit).hasType
  · exact (slots n).term_typed i

private theorem dropVar {Γ L : List (Ty Empty)} {i : Nat} {A : Ty Empty} {r : Region signature.Instr}
    (ha : Tm.HasType Γ (.var i : Tm signature.Instr) A) (hr : ValueBranches (A :: Γ) r L) :
    ValueBranches Γ (r.substVars (Tm.singleSubst (.var i))) L ∧
      Paper.Eqv Γ (.let₁ (.var i) r) (r.substVars (Tm.singleSubst (.var i))) L := by
  cases ha with
  | var hi =>
    refine ⟨hr.substVars ?_, .cfgEta (.native (.letValue (.var hi) hr.hasType))⟩
    intro j B hj
    cases j with
    | zero =>
      have e : A = B := Option.some.inj hj
      subst B
      exact .var hi
    | succ j => exact .var hj

private theorem enterBranch {Γ L : List (Ty Empty)} {k i j : Nat} (hi : i < k + 1)
    {rows : Fin (k + 1) → Region signature.Instr}
    (ht : ValueBranches Γ (.cfg (.br i (.var j)) (k + 1) rows) L) :
    let target := .cfg ((rows ⟨i, hi⟩).substVars (Tm.singleSubst (.var j))) (k + 1) rows
    ValueBranches Γ target L ∧ Paper.Eqv Γ (.cfg (.br i (.var j)) (k + 1) rows) target L := by
  cases ht with
  | cfg R entry hb =>
    cases entry with
    | br atLabel hv =>
      have hR : At (List.ofFn R ++ L) i (R ⟨i, hi⟩) := by
        have bound : i < (List.ofFn R).length := by simpa using hi
        simp only [At, List.getElem?_append_left bound, List.getElem?_ofFn, hi, dite_true]
      cases Option.some.inj (atLabel.symm.trans hR)
      have ⟨targetTyped, beta⟩ := dropVar hv.hasType (hb ⟨i, hi⟩)
      have step := Paper.Eqv.cfgEta (.native (.base (.entry
        (.cfgBrLocal R ⟨i, hi⟩ hv (fun j => (hb j).hasType)))))
      exact ⟨.cfg R targetTyped hb, step.trans (.cfg R beta (fun j => .refl (hb j).hasType))⟩

private theorem enterOne {Γ L : List (Ty Empty)} {e : Region signature.Instr}
    {rows : Fin 1 → Region signature.Instr}
    (ht : ValueBranches Γ (.cfg e 1 rows) L) :
    ValueBranches Γ (e.lsubst (cfgEntryContinuations rows)) L ∧
      Paper.Eqv Γ (.cfg e 1 rows) (e.lsubst (cfgEntryContinuations rows)) L := by
  cases ht with
  | cfg R he hb =>
    have family : LSubst.ValueFamily Γ (List.ofFn R ++ L) L (cfgEntryContinuations rows) :=
      fun _ A h => .cfg R (.br h (.var rfl))
        (fun i => (hb i).renameVars ((Ren.wk Γ A).lift (R i)))
    have constant : (fun _ : Fin 1 => rows 0) = rows :=
      funext fun i => congrArg rows (Subsingleton.elim _ _)
    have entry : ValueBranches Γ e (R 0 :: L) := by simpa using he
    have block : ValueBranches (R 0 :: Γ) (rows 0) (R 0 :: L) := by simpa using hb 0
    have eq := CfgEta.Eqv.eta entry block
    unfold CfgEta.singleCfg CfgEta.reentry at eq
    rw [constant] at eq
    exact ⟨he.lsubst family, .cfgEta eq⟩

private theorem enter_sound {Γ L : List (Ty Empty)} {k : Nat} {e r : Region signature.Instr}
    {rows : Fin k → Region signature.Instr} (ht : ValueBranches Γ (.cfg e k rows) L)
    (h : enter? k e rows = some r) :
    ValueBranches Γ r L ∧ Paper.Eqv Γ (.cfg e k rows) r L := by
  cases found : forwarding e with
  | none =>
    by_cases hk : k = 1
    · subst k
      have target : some (e.lsubst (cfgEntryContinuations rows)) = some r := by
        simpa [enter?, found] using h
      cases Option.some.inj target
      exact enterOne ht
    · simp [enter?, found, hk] at h
  | some dest =>
    obtain ⟨i, j⟩ := dest
    have source : e = .br i (.var j) := by
      fun_cases forwarding e <;> simp_all [forwarding]
    subst e
    by_cases hi : i < k
    · have target : some (.cfg ((rows ⟨i, hi⟩).substVars (Tm.singleSubst (.var j))) k rows) =
          some r := by
        simpa only [enter?, forwarding, hi, dite_true] using h
      cases Option.some.inj target
      cases k with
      | zero => omega
      | succ k => exact enterBranch hi ht
    · simp [enter?, forwarding, hi] at h

private theorem leave {Γ L : List (Ty Empty)} {k : Nat} (R : Fin k → Ty Empty)
    {e r : Region signature.Instr} {rows : Fin k → Region signature.Instr}
    (hb : ∀ i, ValueBranches (R i :: Γ) (rows i) (List.ofFn R ++ L))
    (hr : HasType Γ r L)
    (eq : Paper.Eqv Γ e (r.renameLabels (k + ·)) (List.ofFn R ++ L)) :
    Paper.Eqv Γ (.cfg e k rows) r L := by
  refine (.cfg R eq (fun j => .refl (hb j).hasType) : Paper.Eqv _ _ _ _).trans ?_
  refine .cfgEta (.native ?_)
  cases k with
  | zero =>
    simpa only [Nat.zero_add, show (fun j : Nat => j) = id from rfl, renameLabels_id] using
      SubstitutionEquiv.base (.entry (.cfgZero hr rows))
  | succ k => exact .cfgOutward R hr (fun i => (hb i).hasType)

theorem read_sound (mode : QueryMode) (fuel n : Nat) (pre : List (Ty Empty)) {r : Region signature.Instr} {t : Tree n}
    (hr : ValueBranches (Live n) r (pre ++ Exits)) (h : Readback.readMode mode fuel n pre.length r = some t) :
    Paper.Eqv (Live n) r ((t.regionWithQueries mode.allowVariables (slots n)).renameLabels (pre.length + ·)) (pre ++ Exits)
      ∧ (mode = .forwarded → Direct t) := by
  induction fuel generalizing n pre r with
  | zero => cases h
  | succ fuel ih =>
    cases r with
    | br i a =>
      cases a
      case var j =>
        simp only [Readback.readMode] at h
        split at h
        · rename_i within
          change (if i = pre.length then some (.ret false ⟨j, within⟩)
            else if i = pre.length + 1 then some (.ret true ⟨j, within⟩) else none) = some t at h
          split at h
          · rename_i atExit
            cases h
            refine ⟨?_, fun _ => .ret _ _⟩
            simpa [Tree.regionWithQueries_ret, Tree.region, Slots.terms, slots, renameLabels, atExit] using
              Paper.Eqv.refl hr.hasType
          · split at h
            · rename_i atExit
              cases h
              refine ⟨?_, fun _ => .ret _ _⟩
              simpa [Tree.regionWithQueries_ret, Tree.region, Slots.terms, slots, renameLabels, atExit] using
                Paper.Eqv.refl hr.hasType
            · cases h
        · cases h
      all_goals simp [Readback.readMode] at h
    | case a left right =>
      cases a
      case op f a =>
        cases f with
        | ask label =>
          simp only [Readback.readMode] at h
          obtain ⟨query, hquery, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨r, hright, h⟩ := Option.bind_eq_some_iff.mp h
          cases h
          cases hr with
          | case ha hleft hrightTyped =>
            obtain ⟨rfl, rfl⟩ := requestType ha
            obtain ⟨el, dl⟩ := ih (n + 1) pre hleft hl
            obtain ⟨er, dr⟩ := ih (n + 1) pre hrightTyped hright
            rcases readQuery_spec hquery with ⟨b, rfl, rfl⟩ | ⟨allowed, i, rfl, rfl⟩
            · refine ⟨?_, fun hv => .literal _ _ (dl hv) (dr hv)⟩
              cases b <;> cases mode <;>
                simpa only [Tree.regionWithQueries_ask, QueryMode.allowVariables, queryCase, choose,
                  requestRegion, renameLabels, nextSlot, Bool.false_eq_true, ite_false, ite_true] using
                  Paper.Eqv.case ha el er
            · have mode_eq : mode = .forwarded := by cases mode <;> simp_all [QueryMode.allowVariables]
              subst mode
              refine ⟨?_, fun _ => .var _ _ (dl rfl) (dr rfl)⟩
              simpa only [Tree.regionWithQueries_ask, QueryMode.allowVariables, queryCase,
                ite_true, renameLabels, nextSlot] using Paper.Eqv.case ha el er
      case var j =>
        cases mode with
        | literals => simp [Readback.readMode] at h
        | forwarded => simp [Readback.readMode] at h
        | decisions =>
          simp only [Readback.readMode] at h
          obtain ⟨d, hd, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨r, hright, h⟩ := Option.bind_eq_some_iff.mp h
          cases h
          have regionEq := readDecision_eq hd
          rw [regionEq] at hr ⊢
          obtain ⟨hleft, hrightTyped⟩ := d.branches_typed (slots n).typed hr
          obtain ⟨el, _⟩ := ih (n + 1) pre hleft hl
          obtain ⟨er, _⟩ := ih (n + 1) pre hrightTyped hright
          refine ⟨?_, fun impossible => QueryMode.noConfusion impossible⟩
          have eq := d.replay (slots n).typed (pre.length + ·) el er
          rw [Tree.regionWithQueries_ask, nextSlot]
          change Paper.Eqv _ d.region
            ((⟨d.label, d.query, l.region (slots (n + 1)), r.region (slots (n + 1))⟩ : Decision n).region.renameLabels
              (pre.length + ·)) _
          exact eq
      all_goals simp [Readback.readMode] at h
    | let₁ a body =>
      cases a
      case var j =>
        simp only [Readback.readMode] at h
        cases hr with
        | let₁ ha hbody =>
          obtain ⟨typed, eq⟩ := dropVar ha hbody
          obtain ⟨next, admitted⟩ := ih n pre typed h
          exact ⟨eq.trans next, admitted⟩
      all_goals simp [Readback.readMode] at h
    | let₂ a body => simp [Readback.readMode] at h
    | cfg entry k rows =>
      simp only [Readback.readMode] at h
      cases found : Readback.readMode mode fuel n (k + pre.length) entry with
      | none =>
        rw [found] at h
        obtain ⟨r, outward, rest⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨typed, eq⟩ := enter_sound hr outward
        obtain ⟨next, admitted⟩ := ih n pre typed rest
        exact ⟨eq.trans next, admitted⟩
      | some tt =>
        rw [found] at h
        cases h
        cases hr with
        | cfg R he hb =>
          have found' : Readback.readMode mode fuel n (List.ofFn R ++ pre).length entry = some t := by
            simpa only [List.length_append, List.length_ofFn] using found
          have he' : ValueBranches (Live n) entry ((List.ofFn R ++ pre) ++ Exits) := by
            simpa only [List.append_assoc] using he
          obtain ⟨eq, admitted⟩ := ih n (List.ofFn R ++ pre) he' found'
          simp only [List.append_assoc, List.length_append, List.length_ofFn] at eq
          rw [← show (k + ·) ∘ (pre.length + ·) = (k + pre.length + ·) from
            funext fun j => (Nat.add_assoc k pre.length j).symm, ← renameLabels_comp] at eq
          exact ⟨leave R hb ((t.typedWithQueries mode.allowVariables (slots n)).hasType.renameLabels (labelShift pre)) eq,
            admitted⟩

private theorem firstSlots : slots 1 = inputSlots :=
  slots_ext (funext fun i => congrArg Fin.val (Subsingleton.elim i (0 : Fin 1)))

private theorem packed_eq_quoted {mode : QueryMode} {fuel : Nat} {p : Candidate} {t : Tree 1}
    (quoted : mode.allowVariables = false) (h : Readback.readMode mode fuel 1 0 p.val = some t) :
    p.packed = t.defaultPacked := by
  have step := (read_sound mode fuel 1 [] p.property h).1
  rw [quoted] at step
  change Paper.Eqv [Bit] p.val ((t.region (slots 1)).renameLabels (0 + ·)) Exits at step
  simp only [Nat.zero_add, show (fun j : Nat => j) = id from rfl,
    renameLabels_id, firstSlots] at step
  have eq := Paper.Eqv.lsubstPost step p.property (t.typed inputSlots)
    (fun _ _ hj => (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hj).hasType)
  exact (Paper.TypeCategory.ofRegion_eq_iff p.property.packExits t.guarded_typed.packExits).mpr
    (eq.trans (.cfgEta (.native (native_packed_unguarded t).symm)))

theorem packed_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.read fuel = some t) : p.packed = t.defaultPacked :=
  packed_eq_quoted (mode := .literals) rfl h

theorem packed_eq_decision {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.readWithDecisions fuel = some t) : p.packed = t.defaultPacked :=
  packed_eq_quoted (mode := .decisions) rfl h

theorem observations_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.read fuel = some t) (guard : Bool) : p.observations guard = t.observations guard := by
  unfold Candidate.observations
  rw [packed_eq h]
  rfl

theorem eq_iff_key {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    p.packed = q.packed ↔ t.key = u.key := by
  rw [packed_eq hp, packed_eq hq]
  exact default_eq_iff_key t u

theorem compare_equal {fuel : Nat} {p q : Candidate} (h : Readback.compare fuel p q = .equal) :
    p.packed = q.packed := by
  unfold Readback.compare Readback.compareTrees at h
  split at h
  · rename_i t u hp hq
    split at h
    · rename_i absent
      exact (packed_eq hp).trans (((separate_none_iff_default t u).mp absent).trans (packed_eq hq).symm)
    · cases h
  · cases h

private theorem transfer_difference {p q : Candidate} {t u : Tree 1} {w : Difference}
    (hp : p.observations w.guard = t.observations w.guard)
    (hq : q.observations w.guard = u.observations w.guard) (found : t.separate? u = some w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard := by
  obtain ⟨hsrc, htgt⟩ := separate_some t u found
  cases side : w.fromRight
  · change w.history.observation ∈ p.observations w.guard ∧
      w.history.observation ∉ q.observations w.guard
    rw [hp, hq]
    simp only [Difference.source, Difference.target, side, Bool.false_eq_true, ite_false] at hsrc htgt
    exact ⟨hsrc, htgt⟩
  · change w.history.observation ∈ q.observations w.guard ∧
      w.history.observation ∉ p.observations w.guard
    rw [hp, hq]
    simp only [Difference.source, Difference.target, side, ite_true] at hsrc htgt
    exact ⟨hsrc, htgt⟩

theorem compare_different {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compare fuel p q = .different w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard := by
  unfold Readback.compare Readback.compareTrees at h
  split at h
  · rename_i t u hp hq
    split at h
    · cases h
    · rename_i v found
      cases h
      exact transfer_difference (observations_eq hp w.guard) (observations_eq hq w.guard) found
  · cases h

theorem compare_equal_iff {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    Readback.compare fuel p q = .equal ↔ p.packed = q.packed := by
  constructor
  · exact compare_equal
  · intro eq
    rw [packed_eq hp, packed_eq hq] at eq
    simp only [Readback.compare, Readback.compareTrees, hp, hq, (separate_none_iff_default t u).2 eq]

theorem eq_iff_observations {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    p.packed = q.packed ↔ ∀ guard, p.observations guard = q.observations guard := by
  rw [packed_eq hp, packed_eq hq]
  simp only [observations_eq hp, observations_eq hq]
  exact default_eq_iff_observations t u

private theorem diff_observation_ne {p q : Candidate} {w : Difference}
    (seen : w.history.observation ∈ (if w.fromRight then q else p).observations w.guard)
    (missing : w.history.observation ∉ (if w.fromRight then p else q).observations w.guard) :
    p.packed ≠ q.packed := by
  intro eq
  have same : p.observations w.guard = q.observations w.guard := by
    unfold Candidate.observations
    rw [eq]
  cases side : w.fromRight <;> simp_all

theorem compare_different_ne {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compare fuel p q = .different w) : p.packed ≠ q.packed :=
  diff_observation_ne (compare_different h).1 (compare_different h).2

theorem compare_diff_of_ne {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) (hne : p.packed ≠ q.packed) :
    ∃ w, Readback.compare fuel p q = .different w := by
  have unequal : t.defaultPacked ≠ u.defaultPacked :=
    fun h => hne ((packed_eq hp).trans (h.trans (packed_eq hq).symm))
  obtain ⟨w, hw, _, _⟩ := separate_of_default_ne t u unequal
  exact ⟨w, by simp only [Readback.compare, Readback.compareTrees, hp, hq, hw]⟩

theorem written_packed_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.readWithVariables fuel = some t) : p.packed = t.writtenPacked := by
  have step := (read_sound .forwarded fuel 1 [] p.property h).1
  simp only [List.length_nil, Nat.zero_add, show (fun j : Nat => j) = id from rfl,
    renameLabels_id, firstSlots] at step
  have eq := Paper.Eqv.lsubstPost step p.property (t.typedWithQueries true inputSlots)
    (fun _ _ hj => (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hj).hasType)
  exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr eq

theorem written_observations_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.readWithVariables fuel = some t) (guard : Bool) : p.observations guard = t.observations guard := by
  unfold Candidate.observations
  rw [written_packed_eq h]
  change t.writtenObservations guard = _
  rw [written_packed_outcomes, packed_outcomes]

private theorem quote_same {n : Nat} {e f : Expr n} (h : Expr.quote n e.eval = Expr.quote n f.eval)
    (env : Assignment n) :
    e.eval env = f.eval env := by
  simpa only [Expr.quote_eval] using congrArg (fun q : Expr n => q.eval env) h

private theorem lit_eq {n : Nat} {b c : Bool}
    (h : Expr.quote n (Expr.literal b : Expr n).eval = Expr.quote n (Expr.literal c : Expr n).eval) :
    b = c :=
  quote_same h (fun _ => false)

private theorem lit_ne_read {n : Nat} {b : Bool} {i : Fin n}
    (h : Expr.quote n (Expr.literal b : Expr n).eval = Expr.quote n (Expr.read i).eval) : False := by
  have bad : b = !b := quote_same h (fun _ => !b)
  cases b <;> cases bad

private theorem read_eq {n : Nat} {i j : Fin n}
    (h : Expr.quote n (Expr.read i).eval = Expr.quote n (Expr.read j).eval) : i = j := by
  have same := quote_same h (fun k => decide (k = j))
  simpa [Expr.eval] using same

/-- Each live binder varies independently in the all-replies tree. Thus
a fixed-order Boolean table determines its literal or variable spelling. -/
theorem eq_of_direct_key {n : Nat} {t u : Tree n} (ht : Direct t) (hu : Direct u)
    (h : t.key = u.key) : t = u := by
  induction ht <;> cases hu <;> simp only [Tree.key, Tree.ret.injEq, Tree.ask.injEq] at h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · cases h
  · cases h
  · cases h
  · obtain ⟨rfl, equal, hl, hr⟩ := h
    cases lit_eq equal
    congr 1 <;> solve_by_elim
  · exact False.elim (lit_ne_read h.2.1)
  · cases h
  · exact False.elim (lit_ne_read h.2.1.symm)
  · obtain ⟨rfl, equal, hl, hr⟩ := h
    cases read_eq equal
    congr 1 <;> solve_by_elim

theorem written_eq_iff_key {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.readWithVariables fuel = some t) (hq : q.readWithVariables fuel = some u) :
    p.packed = q.packed ↔ t.key = u.key := by
  constructor
  · intro eq
    apply (default_eq_iff_key t u).1
    apply (default_eq_iff_observations t u).2
    intro guard
    rw [← written_observations_eq hp, ← written_observations_eq hq]
    unfold Candidate.observations
    rw [eq]
  · intro eq
    have ht := (read_sound .forwarded fuel 1 [] p.property hp).2 rfl
    have hu := (read_sound .forwarded fuel 1 [] q.property hq).2 rfl
    have same := eq_of_direct_key ht hu eq
    exact (written_packed_eq hp).trans ((congrArg Tree.writtenPacked same).trans (written_packed_eq hq).symm)

theorem compare_written_equal_iff {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.readWithVariables fuel = some t) (hq : q.readWithVariables fuel = some u) :
    Readback.compareWithVariables fuel p q = .equal ↔ p.packed = q.packed := by
  have key := (separate_none_iff_default t u).trans (default_eq_iff_key t u)
  rw [written_eq_iff_key hp hq, ← key]
  simp only [Readback.compareWithVariables, Readback.compareTrees, hp, hq]
  cases t.separate? u <;> simp

theorem compare_written_different {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compareWithVariables fuel p q = .different w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard := by
  unfold Readback.compareWithVariables Readback.compareTrees at h
  split at h
  · rename_i t u hp hq
    split at h
    · cases h
    · rename_i v found
      cases h
      exact transfer_difference (written_observations_eq hp w.guard) (written_observations_eq hq w.guard) found
  · cases h

theorem compare_written_different_ne {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compareWithVariables fuel p q = .different w) : p.packed ≠ q.packed :=
  diff_observation_ne (compare_written_different h).1 (compare_written_different h).2

theorem observations_eq_decision {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.readWithDecisions fuel = some t) (guard : Bool) : p.observations guard = t.observations guard := by
  unfold Candidate.observations
  rw [packed_eq_decision h]
  rfl

theorem decision_eq_iff_key {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.readWithDecisions fuel = some t) (hq : q.readWithDecisions fuel = some u) :
    p.packed = q.packed ↔ t.key = u.key := by
  rw [packed_eq_decision hp, packed_eq_decision hq]
  exact default_eq_iff_key t u

theorem compare_decision_equal_iff {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.readWithDecisions fuel = some t) (hq : q.readWithDecisions fuel = some u) :
    Readback.compareWithDecisions fuel p q = .equal ↔ p.packed = q.packed := by
  rw [packed_eq_decision hp, packed_eq_decision hq, ← separate_none_iff_default t u]
  simp only [Readback.compareWithDecisions, Readback.compareTrees, hp, hq]
  cases t.separate? u <;> simp

theorem compare_decision_different {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compareWithDecisions fuel p q = .different w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard := by
  unfold Readback.compareWithDecisions Readback.compareTrees at h
  split at h
  · rename_i t u hp hq
    split at h
    · cases h
    · rename_i v found
      cases h
      exact transfer_difference (observations_eq_decision hp w.guard) (observations_eq_decision hq w.guard) found
  · cases h

theorem compare_decision_different_ne {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compareWithDecisions fuel p q = .different w) : p.packed ≠ q.packed :=
  diff_observation_ne (compare_decision_different h).1 (compare_decision_different h).2

namespace Example

open Readback.Example

private theorem joined_typed (right : Bool) (pre Γ : List (Ty Empty)) :
    ValueBranches Γ (joined right pre.length) (pre ++ Exits) := by
  refine .cfg (fun _ => Bit) (.case (.op (constructorBit_value false .unit).hasType)
    (.br rfl (.var (i := 0) rfl)) (.br rfl (.var (i := 0) rfl))) (fun _ => ?_)
  have atExit := labelShift (Bit :: pre) (exit_typed right)
  exact .br (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using atExit)
    (.var (i := 0) rfl)

theorem forward_typed (right : Bool) : ValueBranches [Bit] (forward right) Exits := by
  refine .cfg (fun _ => Bit) (.br rfl (.var (i := 0) rfl)) ?_
  refine Fin.cases (.br rfl (.var (i := 0) rfl)) (fun _ => ?_)
  exact joined_typed right [Bit, Bit] [Bit, Bit]

theorem backward_typed (right : Bool) : ValueBranches [Bit] (backward right) Exits := by
  refine .cfg (fun _ => Bit) (.br rfl (.var (i := 0) rfl)) ?_
  refine Fin.cases ?_ (fun _ => .br rfl (.var (i := 0) rfl))
  exact joined_typed right [Bit, Bit] [Bit, Bit]

end Example

namespace VariableExample

open Readback.VariableExample

private theorem shared_typed (altered : Bool) (pre Γ : List (Ty Empty)) :
    ValueBranches (Bit :: Γ) (shared altered pre.length) (pre ++ Exits) := by
  have firstTag : At (Bit :: Bit :: Γ) (if altered then 1 else 0) Bit := by
    cases altered <;> rfl
  refine .cfg (fun _ => Bit) (.case (.op (constructorBit_value false .unit).hasType)
    (.br rfl (.var (i := 0) rfl)) (.br rfl (.var firstTag))) (fun _ => ?_)
  have atExit : At (List.ofFn (fun _ : Fin 1 => Bit) ++ (pre ++ Exits)) (1 + (pre.length + 1)) Bit := by
    have shifted := labelShift (Bit :: pre) (exit_typed true)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using shifted
  exact .let₁ (.var (i := 0) rfl)
    (.case (.op (.var (i := 1) rfl)) (.br atExit (.var (i := 0) rfl)) (.br atExit (.var (i := 0) rfl)))

theorem numbered_typed (renumbered altered : Bool) : ValueBranches [Bit] (numbered renumbered altered) Exits := by
  cases renumbered
  · refine .cfg (fun _ => Bit) (.br rfl (.var (i := 0) rfl)) ?_
    exact Fin.cases (.br rfl (.var (i := 0) rfl)) (fun _ => shared_typed altered [Bit, Bit] [Bit])
  · refine .cfg (fun _ => Bit) (.br rfl (.var (i := 0) rfl)) ?_
    exact Fin.cases (shared_typed altered [Bit, Bit] [Bit]) (fun _ => .br rfl (.var (i := 0) rfl))

theorem effectful_query_typed : ValueBranches [Bit] effectfulQuery Exits :=
  call_typed true (.case (.op (constructorBit_value false .unit).hasType)
    (.var (i := 0) rfl) (.var (i := 0) rfl))

end VariableExample

namespace DecisionExample

open Readback.DecisionExample

private theorem request_row_typed (b : Bool) {Γ L : List (Ty Empty)} {offset : Nat}
    (exit : At L (offset + 1) Bit) : ValueBranches Γ (request b offset) L :=
  .case (.op (constructorBit_value b .unit).hasType)
    (.br exit (.var (i := 0) rfl)) (.br exit (.var (i := 0) rfl))

private theorem staged_typed (shape : Shape) {Γ L : List (Ty Empty)} {offset : Nat}
    (exit : At L (offset + 1) Bit) : ValueBranches (Bit :: Bit :: Γ) (staged shape offset) L := by
  cases shape
  · exact .case (.var (i := 0) rfl) (request_row_typed false exit) (request_row_typed true exit)
  · exact .case (.var (i := 0) rfl) (request_row_typed false exit)
      (.case (.var (i := 2) rfl) (request_row_typed true exit) (request_row_typed true exit))
  · exact .case (.var (i := 0) rfl) (request_row_typed false exit)
      (.case (.var (i := 2) rfl) (request_row_typed false exit) (request_row_typed true exit))

theorem numbered_typed (renumbered : Bool) (shape : Shape) :
    ValueBranches [Bit] (numbered renumbered shape) Exits := by
  have row : ValueBranches [Bit, Bit] (entry shape) ([Bit, Bit] ++ Exits) :=
    .case (.op (constructorBit_value false .unit).hasType)
      (request_row_typed false rfl) (staged_typed shape rfl)
  cases renumbered
  · exact .cfg (fun _ => Bit) (.br rfl (.var (i := 0) rfl))
      (Fin.cases (.br rfl (.var (i := 0) rfl)) (fun _ => row))
  · exact .cfg (fun _ => Bit) (.br rfl (.var (i := 0) rfl))
      (Fin.cases row (fun _ => .br rfl (.var (i := 0) rfl)))

theorem term_case_typed : ValueBranches [Bit] termCase Exits :=
  call_typed false (.case (.var (i := 0) rfl)
    (constructorBit_value false .unit).hasType (constructorBit_value true .unit).hasType)

theorem term_case_packed_of (beta : Readback.CaseOperandBeta) :
    Paper.TypeCategory.ofRegion term_case_typed.packExits = quotedTermCase.defaultPacked := by
  have left : ValueBranches [Bit, Bit] (.br 0 (.var 0) : Region signature.Instr) Exits :=
    .br rfl (.var (i := 0) rfl)
  have right : ValueBranches [Bit, Bit] (.br 1 (.var 0) : Region signature.Instr) Exits :=
    .br rfl (.var (i := 0) rfl)
  have step : Paper.Eqv [Bit] termCase (quotedTermCase.region inputSlots) Exits :=
    Readback.term_case_operand_of beta (i := 0) rfl false left right
  have packedStep := Paper.Eqv.lsubstPost step term_case_typed (quotedTermCase.typed inputSlots)
    (fun _ _ hj => (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hj).hasType)
  exact (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr (packedStep.trans
    (.cfgEta (.native (native_packed_unguarded quotedTermCase).symm)))

theorem expected_ne : expected .plain ≠ expected .redundant := by
  simp [expected, selectedQuery, rightQuery]

end DecisionExample

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeReadback
