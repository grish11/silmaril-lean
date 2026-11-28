module

public import Silmaril.Languages.Starlark.Lists.Comparison.Operational.Defs
import Silmaril.Languages.Starlark.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists.Comparison

open Silmaril.Languages
open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark.Lists.Comparison

theorem scans_iff_scan {α : Type} {tests : α → Except Error Bool → Prop}
    {test : α → Except Error Bool} (agrees : ∀ item out, tests item out ↔ test item = out)
    (decisive : Bool) (items : List α) (out : Except Error Bool) :
    Scans tests decisive items out ↔ scan test decisive items = out := by
  constructor
  · intro runs
    induction runs with
    | empty => rfl
    | stopped hit => simp [scan, (agrees _ _).mp hit]
    | failed fails => simp [scan, (agrees _ _).mp fails]
    | continued misses _ ih =>
      cases decisive <;> simpa [scan, (agrees _ _).mp misses] using ih
  · intro runs
    subst out
    induction items with
    | nil => exact .empty
    | cons item rest ih =>
      rw [scan]
      cases got : test item with
      | error error => exact .failed ((agrees _ _).mpr got)
      | ok flag =>
        by_cases stops : flag = decisive
        · subst flag
          simpa using Scans.stopped (rest := rest) ((agrees _ _).mpr got)
        · have misses : flag = !decisive := by
            cases flag <;> cases decisive <;> simp_all
          subst flag
          simpa [stops] using Scans.continued ((agrees _ _).mpr got) ih

private theorem scalar_result (left right : Starlark.Value) :
    Starlark.applyBinary .eq left right = .ok (.bool (scalarEqual left right)) := by
  cases order : left.orderedCompare right <;>
    simp [Starlark.applyBinary, Starlark.comparisonResult, scalarEqual, order]

theorem looksUp_iff_findEntry (key : Key) (entries : List Entry) (out : Option Entry) :
    LooksUp key entries out ↔ findEntry key entries = out := by
  constructor
  · intro ran
    induction ran <;> simp_all [findEntry, beq_iff_eq]
  · intro ran
    subst out
    induction entries with
    | nil => exact .missing
    | cons entry rest ih =>
      by_cases hit : entry.keyCode = key
      · simpa [findEntry, beq_iff_eq, hit] using LooksUp.hit (rest := rest) hit
      · simpa [findEntry, beq_iff_eq, hit] using LooksUp.skip hit ih

theorem dictionaryLookup_iff (heap : Heap) (address : Address) (key : Value)
    (out : Except Error (Option Entry)) :
    DictionaryLookup heap address key out ↔ lookupDictionary heap address key = out := by
  constructor
  · intro ran
    cases ran with
    | receiverError read => simp [lookupDictionary, read, Except.bind, bind]
    | keyError read encoded => simp [lookupDictionary, read, encoded, Except.bind, bind]
    | searched read encoded found =>
      simp [lookupDictionary, read, encoded, Except.bind, bind, pure, Except.pure,
        (looksUp_iff_findEntry ..).mp found]
  · intro ran
    subst out
    cases read : dictionaryEntries heap address with
    | error error =>
      simpa [lookupDictionary, read, Except.bind, bind] using
        DictionaryLookup.receiverError (key := key) read
    | ok entries =>
      cases encoded : ({ heap := heap } : State).keyOf key with
      | error error =>
        simpa [lookupDictionary, read, encoded, Except.bind, bind] using
          DictionaryLookup.keyError read encoded
      | ok code =>
        simpa [lookupDictionary, read, encoded, Except.bind, bind, pure, Except.pure] using
          DictionaryLookup.searched read encoded ((looksUp_iff_findEntry code entries _).mpr rfl)

theorem probes_iff_probe {α : Type} {tests : α → Except Error Bool → Prop}
    {test : α → Except Error Bool} (agree : ∀ item out, tests item out ↔ test item = out)
    (candidates : List α) (out : Except Error (Option α)) :
    Probes tests candidates out ↔ probe test candidates = out := by
  constructor
  · intro ran
    induction ran with
    | missing => rfl
    | hit h => simp [probe, (agree ..).mp h]
    | failed h => simp [probe, (agree ..).mp h]
    | skip h _ ih => simpa [probe, (agree ..).mp h] using ih
  · intro ran
    subst out
    induction candidates with
    | nil => exact .missing
    | cons candidate later ih =>
      rw [probe]
      cases checked : test candidate with
      | error error => exact .failed ((agree ..).mpr checked)
      | ok flag =>
        cases flag with
        | true => exact .hit ((agree ..).mpr checked)
        | false => exact .skip ((agree ..).mpr checked) ih

theorem probe_cached (key : Key) (entries : List Entry) :
    probe (fun entry : Entry => .ok (entry.keyCode == key)) entries = .ok (findEntry key entries) := by
  induction entries with
  | nil => rfl
  | cons entry later ih => cases hit : entry.keyCode == key <;> simp [probe, findEntry, hit, ih]

theorem findEntry_some_iff_of_unique (key : Key) (entries : List Entry) (entry : Entry)
    (unique : UniqueKeyCodes entries) :
    findEntry key entries = some entry ↔ entry ∈ entries ∧ entry.keyCode = key := by
  constructor
  · intro found
    have matched := List.find?_some (p := fun candidate : Entry => candidate.keyCode == key) found
    exact ⟨List.mem_of_find?_eq_some found, beq_iff_eq.mp matched⟩
  · rintro ⟨mem, hKey⟩
    induction entries with
    | nil => simp at mem
    | cons old rest ih =>
      have parts := List.pairwise_cons.mp unique
      rcases List.mem_cons.mp mem with rfl | inRest
      · simp [findEntry, hKey]
      · have misses : old.keyCode ≠ key := hKey ▸ parts.1 entry inRest
        simpa [findEntry, beq_iff_eq, misses] using ih parts.2 inRest

theorem uniqueKeyCodes_append_of_missing (entry : Entry) (entries : List Entry)
    (unique : UniqueKeyCodes entries) (missing : findEntry entry.keyCode entries = none) :
    UniqueKeyCodes (entries ++ [entry]) := by
  have absent := List.find?_eq_none.mp missing
  simp only [UniqueKeyCodes, List.pairwise_append, List.pairwise_singleton, List.mem_singleton,
    true_and, forall_eq]
  exact ⟨unique, fun old mem matched => absent old mem (beq_iff_eq.mpr matched)⟩

private theorem putEntry_avoids (code : Key) (entry : Entry) (entries : List Entry)
    (different : code ≠ entry.keyCode) (absent : ∀ old ∈ entries, code ≠ old.keyCode) :
    ∀ item ∈ putEntry entry entries, code ≠ item.keyCode := by
  induction entries with
  | nil => simpa [putEntry] using different
  | cons old rest ih =>
    have headMissing := absent old (List.mem_cons_self ..)
    have tailMissing : ∀ item ∈ rest, code ≠ item.keyCode :=
      fun item mem => absent item (List.mem_cons_of_mem _ mem)
    by_cases same : old.keyCode = entry.keyCode
    · simpa [putEntry, beq_iff_eq, same] using And.intro headMissing tailMissing
    · simpa [putEntry, beq_iff_eq, same] using And.intro headMissing (ih tailMissing)

theorem uniqueKeyCodes_putEntry (entry : Entry) (entries : List Entry)
    (unique : UniqueKeyCodes entries) : UniqueKeyCodes (putEntry entry entries) := by
  induction entries with
  | nil => simp [UniqueKeyCodes, putEntry]
  | cons old rest ih =>
    have parts := List.pairwise_cons.mp unique
    by_cases same : old.keyCode = entry.keyCode
    · simpa [UniqueKeyCodes, putEntry, beq_iff_eq, same, List.pairwise_cons] using parts
    · simpa [UniqueKeyCodes, putEntry, beq_iff_eq, same, List.pairwise_cons] using
        And.intro (putEntry_avoids old.keyCode entry rest same parts.1) (ih parts.2)

private theorem comparesEntry_iff_compareEntry {next : Value → Value → Except Error Bool → Prop}
    {equal : Value → Value → Except Error Bool}
    (agree : ∀ a b out, next a b out ↔ equal a b = out)
    (right : List Entry) (left : Entry) (out : Except Error Bool) :
    ComparesEntry next right left out ↔ compareEntry equal right left = out := by
  have lookup := looksUp_iff_findEntry left.keyCode right
  constructor
  · intro ran
    cases ran with
    | missing miss => simp [compareEntry, (lookup _).mp miss]
    | found hit compared => simp [compareEntry, (lookup _).mp hit, (agree ..).mp compared]
  · intro ran
    subst out
    unfold compareEntry
    cases eq : findEntry left.keyCode right with
    | none => exact .missing ((lookup _).mpr eq)
    | some entry => exact .found ((lookup _).mpr eq) ((agree ..).mpr rfl)

theorem equalAt_iff (heap : Heap) (depth : Nat) (left right : Value)
    (out : Except Error Bool) :
    EqualAt heap depth left right out ↔ equalAt heap depth left right = out := by
  induction depth generalizing left right out with
  | zero => exact eq_comm
  | succ depth ih =>
    rw [EqualAt, equalAt]
    constructor
    · intro runs
      cases runs with
      | scalar route compares =>
        have computed := ((Starlark.compares_iff_applyBinary ..).mp compares).2
        rw [scalar_result] at computed
        simpa [route] using computed
      | string route => simp [route]
      | different route | unsupported route => simp [route]
      | leftError route read => simp [route, read, Except.bind, bind]
      | rightError route first second => simp [route, first, second, Except.bind, bind]
      | lengthMismatch route first second lengths =>
        simp [route, first, second, lengths, Except.bind, bind, pure, Except.pure]
      | fields route first second lengths runs =>
        simpa [route, first, second, lengths, Except.bind, bind] using
          (scans_iff_scan (fun (pair : Value × Value) => ih pair.1 pair.2) ..).mp runs
      | dictLeftError route read => simp [route, read, Except.bind, bind]
      | dictRightError route first second => simp [route, first, second, Except.bind, bind]
      | dictLengthMismatch route first second lengths =>
        simp [route, first, second, lengths, Except.bind, bind, pure, Except.pure]
      | dictEntries route first second lengths runs =>
        simpa [route, first, second, lengths, Except.bind, bind] using
          (scans_iff_scan (comparesEntry_iff_compareEntry ih _) ..).mp runs
    · intro runs
      subst out
      cases route : Pair.ofValues left right with
      | scalars a b =>
        exact .scalar route ((Starlark.compares_iff_applyBinary ..).mpr ⟨rfl, scalar_result a b⟩)
      | strings a b => exact .string route
      | different => exact .different route
      | unsupported => exact .unsupported route
      | sequences kind a b =>
        cases first : kind.elements heap a with
        | error error =>
          simpa [first, Except.bind, bind] using
            EqualStep.leftError (next := EqualAt heap depth) route first
        | ok xs =>
          cases second : kind.elements heap b with
          | error error =>
            simpa [first, second, Except.bind, bind] using
              EqualStep.rightError (next := EqualAt heap depth) route first second
          | ok ys =>
            by_cases lengths : xs.length = ys.length
            · simpa [first, second, lengths, Except.bind, bind] using
                EqualStep.fields route first second lengths
                  ((scans_iff_scan (fun (pair : Value × Value) => ih pair.1 pair.2) ..).mpr rfl)
            · simpa [first, second, lengths, Except.bind, bind, pure, Except.pure] using
                EqualStep.lengthMismatch (next := EqualAt heap depth) route first second lengths
      | dictionaries a b =>
        cases first : dictionaryEntries heap a with
        | error error =>
          simpa [first, Except.bind, bind] using
            EqualStep.dictLeftError (next := EqualAt heap depth) route first
        | ok xs =>
          cases second : dictionaryEntries heap b with
          | error error =>
            simpa [first, second, Except.bind, bind] using
              EqualStep.dictRightError (next := EqualAt heap depth) route first second
          | ok ys =>
            by_cases lengths : xs.length = ys.length
            · simpa [first, second, lengths, Except.bind, bind] using
                EqualStep.dictEntries route first second lengths
                  ((scans_iff_scan (comparesEntry_iff_compareEntry ih ys) ..).mpr rfl)
            · simpa [first, second, lengths, Except.bind, bind, pure, Except.pure] using
                EqualStep.dictLengthMismatch (next := EqualAt heap depth) route first second lengths

theorem containsAt_iff (heap : Heap) (depth : Nat) (needle target : Value)
    (out : Except Error Bool) :
    ContainsAt heap depth needle target out ↔ containsAt heap depth needle target = out := by
  constructor
  · intro runs
    cases runs with
    | unsupported route => simp [containsAt, route]
    | readError route read => simp [containsAt, route, read, Except.bind, bind]
    | fields route read runs =>
      simpa [containsAt, route, read, Except.bind, bind] using
        (scans_iff_scan (fun field => equalAt_iff heap depth field needle) ..).mp runs
    | dictionary route ran => simp only [containsAt, route, (dictionaryLookup_iff ..).mp ran]
  · intro runs
    subst out
    cases route : MembershipTarget.ofValue target with
    | unsupported =>
      simpa [containsAt, route] using
        ContainsAt.unsupported (heap := heap) (depth := depth) (needle := needle) route
    | dictionary address =>
      simpa [containsAt, route] using
        ContainsAt.dictionary (depth := depth) route ((dictionaryLookup_iff heap address needle _).mpr rfl)
    | sequence kind address =>
      cases read : kind.elements heap address with
      | error error =>
        simpa [containsAt, route, read, Except.bind, bind] using
          ContainsAt.readError (depth := depth) (needle := needle) route read
      | ok fields =>
        simpa [containsAt, route, read, Except.bind, bind] using
          ContainsAt.fields route read
            ((scans_iff_scan (fun field => equalAt_iff heap depth field needle) ..).mpr rfl)

theorem tests_iff_evaluate (heap : Heap) (left right : Value) (op : ComparisonOp)
    (out : Except Error Bool) :
    Tests heap left right op out ↔ evaluate heap op left right = out := by
  have eq := equalAt_iff heap defaultDepth left right
  have mem := containsAt_iff heap defaultDepth left right
  constructor
  · intro runs
    cases runs with
    | eq runs => exact (eq _).mp runs
    | ne runs => simp only [evaluate, (eq _).mp runs]
    | mem runs => exact (mem _).mp runs
    | notMem runs => simp only [evaluate, (mem _).mp runs]
  · intro runs
    subst out
    cases op with
    | eq => exact .eq ((eq _).mpr rfl)
    | ne => exact .ne ((eq _).mpr rfl)
    | mem => exact .mem ((mem _).mpr rfl)
    | notMem => exact .notMem ((mem _).mpr rfl)

end Silmaril.Proofs.Languages.Starlark.Lists.Comparison
