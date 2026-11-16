module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Defs

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
open Silmaril.Logic Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites
open Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source

/-- The payload smart constructor retains exact source, budget and original
visibility scope rather than accepting caller-provided provenance fields. -/
theorem checkPayload_source {ambient scope cfg fuel raw}
    {p : AcceptedRule ambient cfg}
    (h : checkPayload ambient scope cfg fuel raw = some p) :
    p.source = raw ∧ p.fuel = fuel ∧ p.declaringScope = scope := by
  unfold checkPayload at h
  split at h
  · split at h
    · contradiction
    · cases Option.some.inj h
      exact ⟨rfl, rfl, rfl⟩
  · contradiction

/-- Successful operational definition checking retains the actual original
module source and proves configuration-sort declaration even for empty systems. -/
theorem checkDefinition_source {cfg fuel source} {result : CheckedDefinition cfg}
    (h : checkDefinition cfg fuel source = some result) :
    result.source = source ∧ Kore.Modules.Checking.namedSort result.ambient cfg = true := by
  unfold checkDefinition at h
  obtain ⟨⟨ambient, modules⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · contradiction
  · rename_i declared
    cases Option.some.inj h
    exact ⟨rfl, by simpa using declared⟩

/-- Every retained element comes from an actual successful source callback. -/
theorem filterMapM_mem {α β : Type} (f : α → Option (Option β))
    (xs : List α) {ys : List β} {y : β}
    (h : xs.filterMapM f = some ys) (member : y ∈ ys) :
    ∃ x ∈ xs, f x = some (some y) := by
  induction xs generalizing ys with
  | nil =>
      change some [] = some ys at h
      have same := Option.some.inj h
      subst ys
      contradiction
  | cons x xs ih =>
      cases hx : f x with
      | none => simp [hx] at h
      | some value =>
          cases value with
          | none =>
              have tail : xs.filterMapM f = some ys := by simpa [hx] using h
              obtain ⟨z, hz, source⟩ := ih tail member
              exact ⟨z, List.mem_cons_of_mem x hz, source⟩
          | some z =>
              cases ht : xs.filterMapM f with
              | none => simp [hx, ht] at h
              | some tail =>
                  have same : z :: tail = ys := by simpa [hx, ht] using h
                  subst ys
                  rcases List.mem_cons.mp member with same | rest
                  · subst z
                    exact ⟨x, List.mem_cons_self, hx⟩
                  · obtain ⟨w, hw, source⟩ := ih ht rest
                    exact ⟨w, List.mem_cons_of_mem x hw, source⟩

/-- Every retained local rule comes from an actual zipped source declaration,
with its kind, original index/location and successful payload check retained. -/
theorem localRules_source {ambient scope cfg fuel m claims}
    {rules : List (LocatedRule ambient cfg)} {r : LocatedRule ambient cfg}
    (h : localRules ambient scope cfg fuel m claims = some rules) (hr : r ∈ rules) :
    ∃ (d : Kore.Modules.LocatedDeclaration Raw) (i : Nat) (raw : Raw),
      (d, i) ∈ m.declarations.zipIdx ∧
      d.declaration = (if claims then .claim raw else .ruleAxiom raw) ∧
      r.origin = ⟨m.name, i⟩ ∧ r.location = d.location ∧ r.isClaim = claims ∧
      r.payload.source = raw ∧ r.payload.fuel = fuel ∧ r.payload.declaringScope = scope ∧
      checkPayload ambient scope cfg fuel raw = some r.payload := by
  unfold localRules at h
  obtain ⟨⟨d, i⟩, member, accepted⟩ := filterMapM_mem _ _ h hr
  dsimp only at accepted
  cases hd : d.declaration with
  | ruleAxiom raw =>
      cases hc : claims with
      | true => simp [hd, hc] at accepted
      | false =>
          simp only [hd, hc] at accepted
          change (checkPayload ambient scope cfg fuel raw >>= fun payload =>
            some (some (⟨⟨m.name, i⟩, d.location, false, payload⟩ : LocatedRule ambient cfg))) =
              some (some r) at accepted
          obtain ⟨payload, hp, eq⟩ := Option.bind_eq_some_iff.mp accepted
          have same : (⟨⟨m.name, i⟩, d.location, false, payload⟩ : LocatedRule ambient cfg) = r :=
            Option.some.inj (Option.some.inj eq)
          subst r
          obtain ⟨rawSource, budget, scopeEq⟩ := checkPayload_source hp
          exact ⟨d, i, raw, member, hd, rfl, rfl, rfl, rawSource, budget, scopeEq, hp⟩
  | claim raw =>
      cases hc : claims with
      | false => simp [hd, hc] at accepted
      | true =>
          simp only [hd, hc] at accepted
          change (checkPayload ambient scope cfg fuel raw >>= fun payload =>
            some (some (⟨⟨m.name, i⟩, d.location, true, payload⟩ : LocatedRule ambient cfg))) =
              some (some r) at accepted
          obtain ⟨payload, hp, eq⟩ := Option.bind_eq_some_iff.mp accepted
          have same : (⟨⟨m.name, i⟩, d.location, true, payload⟩ : LocatedRule ambient cfg) = r :=
            Option.some.inj (Option.some.inj eq)
          subst r
          obtain ⟨rawSource, budget, scopeEq⟩ := checkPayload_source hp
          exact ⟨d, i, raw, member, hd, rfl, rfl, rfl, rawSource, budget, scopeEq, hp⟩
  | importModule name => cases hc : claims <;> simp [hd, hc] at accepted
  | sort name => cases hc : claims <;> simp [hd, hc] at accepted
  | hookedSort name hook => cases hc : claims <;> simp [hd, hc] at accepted
  | symbol symbol => cases hc : claims <;> simp [hd, hc] at accepted
  | hookedSymbol symbol hook => cases hc : claims <;> simp [hd, hc] at accepted
  | «alias» declaration => cases hc : claims <;> simp [hd, hc] at accepted

/-- Successful module checking fixes its original source, ordered imports,
computed scope and the exact two distinct source declaration selections. -/
theorem checkModule_source {ambient cfg fuel earlier m}
    {result : CheckedModule ambient cfg}
    (h : checkModule ambient cfg fuel earlier m = some result) :
    result.source = m ∧ result.fuel = fuel ∧
    (∃ names, m.orderedImports = some names ∧
      names.mapM (fun name =>
        (earlier.find? (fun p => p.source.name == name)).map CheckedModule.asImport) =
          some result.imports) ∧
    result.scope = result.imports.foldl (fun scope p => scope.merge p.scope) m.localScope ∧
    localRules ambient result.scope cfg fuel m false = some result.localAxioms ∧
    localRules ambient result.scope cfg fuel m true = some result.claims := by
  unfold checkModule at h
  split at h
  · contradiction
  · obtain ⟨names, namesChecked, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨parents, parentsChecked, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · contradiction
    · obtain ⟨axioms, axiomsChecked, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨claims, claimsChecked, h⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj h
      exact ⟨rfl, rfl, ⟨names, namesChecked, parentsChecked⟩, rfl,
        axiomsChecked, claimsChecked⟩

/-- Local installed entries really are axioms at their original source index;
this theorem assumes only successful checking and list membership. -/
theorem checkModule_local_axiom_source {ambient cfg fuel earlier m}
    {result : CheckedModule ambient cfg} {r : LocatedRule ambient cfg}
    (h : checkModule ambient cfg fuel earlier m = some result)
    (member : r ∈ result.localAxioms) :
    ∃ (d : Kore.Modules.LocatedDeclaration Raw) (i : Nat) (raw : Raw),
      (d, i) ∈ m.declarations.zipIdx ∧ d.declaration = .ruleAxiom raw ∧
      r.origin = ⟨m.name, i⟩ ∧ r.location = d.location ∧ r.isClaim = false ∧
      r.payload.source = raw ∧ r.payload.fuel = fuel ∧
      r.payload.declaringScope = result.scope ∧
      checkPayload ambient result.scope cfg fuel raw = some r.payload := by
  obtain ⟨_, _, _, _, axioms, _⟩ := checkModule_source h
  exact localRules_source axioms member

/-- Claims are checked separately and retain their original source kind. -/
theorem checkModule_local_claim_source {ambient cfg fuel earlier m}
    {result : CheckedModule ambient cfg} {r : LocatedRule ambient cfg}
    (h : checkModule ambient cfg fuel earlier m = some result)
    (member : r ∈ result.claims) :
    ∃ (d : Kore.Modules.LocatedDeclaration Raw) (i : Nat) (raw : Raw),
      (d, i) ∈ m.declarations.zipIdx ∧ d.declaration = .claim raw ∧
      r.origin = ⟨m.name, i⟩ ∧ r.location = d.location ∧ r.isClaim = true ∧
      r.payload.source = raw ∧ r.payload.fuel = fuel ∧
      r.payload.declaringScope = result.scope ∧
      checkPayload ambient result.scope cfg fuel raw = some r.payload := by
  obtain ⟨_, _, _, _, _, claims⟩ := checkModule_source h
  exact localRules_source claims member

/-- Actual successful module-checking history, independent of an axiom-kind
invariant. Each extension names the original module and the real checker call. -/
inductive CheckedHistory (source : Kore.Modules.Definition Raw)
    (ambient : Kore.Modules.Scope) (cfg : String) (fuel : Nat) :
    List (CheckedModule ambient cfg) → Prop where
  | empty : CheckedHistory source ambient cfg fuel []
  | append {earlier m checked} : CheckedHistory source ambient cfg fuel earlier →
      m ∈ source.modules → checkModule ambient cfg fuel earlier m = some checked →
      CheckedHistory source ambient cfg fuel (earlier ++ [checked])

/-- The actual monadic module fold constructs a history; no result invariant is
supplied by the caller. The prior history is only the fold's induction state. -/
theorem moduleFold_history {source ambient cfg fuel}
    (remaining : List (Kore.Modules.Module Raw))
    (inSource : ∀ m ∈ remaining, m ∈ source.modules)
    (earlier : List (CheckedModule ambient cfg))
    (prior : CheckedHistory source ambient cfg fuel earlier)
    {result : List (CheckedModule ambient cfg)}
    (h : remaining.foldlM (fun earlier m => do
      let checked ← checkModule ambient cfg fuel earlier m
      pure (earlier ++ [checked])) earlier = some result) :
    CheckedHistory source ambient cfg fuel result := by
  induction remaining generalizing earlier with
  | nil =>
      change some earlier = some result at h
      have same := Option.some.inj h
      subst result
      exact prior
  | cons m rest ih =>
      simp only [List.foldlM_cons] at h
      obtain ⟨next, nextChecked, restChecked⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨checked, moduleChecked, same⟩ := Option.bind_eq_some_iff.mp nextChecked
      cases Option.some.inj same
      exact ih (fun m hm => inSource m (List.mem_cons_of_mem _ hm))
        (earlier ++ [checked])
        (.append prior (inSource m List.mem_cons_self) moduleChecked) restChecked

theorem traverse_history {cfg fuel source}
    {result : Σ ambient : Kore.Modules.Scope, List (CheckedModule ambient cfg)}
    (h : Kore.Modules.Checking.traverseDefinitionWith
      (fun ambient earlier m => checkModule ambient cfg fuel earlier m) source = some result) :
    CheckedHistory source result.1 cfg fuel result.2 := by
  unfold Kore.Modules.Checking.traverseDefinitionWith at h
  split at h
  · contradiction
  · dsimp only at h
    split at h
    · contradiction
    · obtain ⟨modules, folded, same⟩ := Option.bind_eq_some_iff.mp h
      cases Option.some.inj same
      exact moduleFold_history source.modules (fun _ h => h) [] .empty folded

/-- Accepted definitions inherit actual checking histories, including imports
resolved against the precise earlier prefix. -/
theorem checkDefinition_history {cfg fuel source} {result : CheckedDefinition cfg}
    (h : checkDefinition cfg fuel source = some result) :
    CheckedHistory source result.ambient cfg fuel result.modules := by
  unfold checkDefinition at h
  obtain ⟨built, checked, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · contradiction
  · cases Option.some.inj h
    exact traverse_history checked

/-- Successful monadic mapping retains an original input for each output. -/
theorem mapM_mem {α β : Type} (f : α → Option β) (xs : List α)
    {ys : List β} {y : β} (h : xs.mapM f = some ys) (member : y ∈ ys) :
    ∃ x ∈ xs, f x = some y := by
  induction xs generalizing ys with
  | nil =>
      change some [] = some ys at h
      have same := Option.some.inj h
      subst ys
      contradiction
  | cons x xs ih =>
      cases hx : f x with
      | none => simp [hx] at h
      | some z =>
          cases ht : xs.mapM f with
          | none => simp [hx, ht] at h
          | some tail =>
              have same : z :: tail = ys := by simpa [hx, ht] using h
              subst ys
              rcases List.mem_cons.mp member with same | rest
              · subst z
                exact ⟨x, List.mem_cons_self, hx⟩
              · obtain ⟨w, hw, source⟩ := ih ht rest
                exact ⟨w, List.mem_cons_of_mem x hw, source⟩

/-- A genuine path through original source import lists. The edge condition
runs the existing ordered-import reader on an actual source module. -/
inductive ImportPath (source : Kore.Modules.Definition Raw) : String → String → Prop where
  | here {m} : m ∈ source.modules → ImportPath source m.name m.name
  | via {m names parent target} : m ∈ source.modules →
      m.orderedImports = some names → parent ∈ names →
      ImportPath source parent target → ImportPath source m.name target

/-- Exact original axiom declaration and original source import path, together
with source kind, zip index, location, raw body, budget and successful checking. -/
def InstalledSource {ambient cfg} (source : Kore.Modules.Definition Raw)
    (fuel : Nat) (moduleName : String) (r : LocatedRule ambient cfg) : Prop :=
  ∃ (m : Kore.Modules.Module Raw) (d : Kore.Modules.LocatedDeclaration Raw)
      (i : Nat) (raw : Raw),
    m ∈ source.modules ∧ ImportPath source moduleName m.name ∧
    (d, i) ∈ m.declarations.zipIdx ∧ d.declaration = .ruleAxiom raw ∧
    r.origin = ⟨m.name, i⟩ ∧ r.location = d.location ∧ r.isClaim = false ∧
    r.payload.source = raw ∧ r.payload.fuel = fuel ∧
    checkPayload ambient r.payload.declaringScope cfg fuel raw = some r.payload ∧
    checkRewrite ambient cfg fuel raw.rewrite = some r.payload.checked ∧
    visible r.payload.declaringScope fuel raw = true

/-- Actual checker histories establish installed-source provenance inductively.
Imported entries are traced through real mapM/find? parent resolution; no
axiom-kind or provenance invariant is assumed for the result. -/
theorem CheckedHistory.installedSource {source ambient cfg fuel modules}
    (history : CheckedHistory source ambient cfg fuel modules) :
    ∀ (m : CheckedModule ambient cfg), m ∈ modules →
      ∀ r ∈ m.axioms, InstalledSource source fuel m.source.name r := by
  induction history with
  | empty => intro m member; simp at member
  | @append earlier original checked prior inSource accepted ih =>
      intro m member r installed
      rcases List.mem_append.mp member with old | newest
      · exact ih m old r installed
      · have same : m = checked := by simpa using newest
        subst m
        have sourceEq := (checkModule_source accepted).1
        change r ∈ checked.localAxioms ++ checked.imports.flatMap Import.axioms at installed
        rcases List.mem_append.mp installed with localEntry | imported
        · obtain ⟨d, i, raw, member, kind, origin, location, isClaim,
              rawSource, budget, scopeEq, payloadChecked⟩ :=
            checkModule_local_axiom_source accepted localEntry
          refine ⟨original, d, i, raw, inSource, ?_, member, kind, origin, location,
            isClaim, rawSource, budget, ?_, ?_, ?_⟩
          · simpa only [sourceEq] using (ImportPath.here inSource)
          · simpa only [scopeEq] using payloadChecked
          · simpa only [rawSource, budget] using r.payload.accepted
          · simpa only [rawSource, budget] using r.payload.visible
        · obtain ⟨parent, parentMember, ruleMember⟩ := List.mem_flatMap.mp imported
          obtain ⟨_, _, ⟨names, ordered, parentChecks⟩, _, _, _⟩ := checkModule_source accepted
          obtain ⟨name, nameMember, parentChecked⟩ := mapM_mem _ _ parentChecks parentMember
          obtain ⟨previous, found, sameParent⟩ := Option.map_eq_some_iff.mp parentChecked
          have previousMember : previous ∈ earlier := List.mem_of_find?_eq_some found
          have sameName : previous.source.name = name := by
            simpa using (List.find?_some found)
          rw [← sameParent] at ruleMember
          have provenance := ih previous previousMember r ruleMember
          obtain ⟨declaring, d, i, raw, declaringMember, path, member, kind,
            origin, location, isClaim, rawSource, budget, payloadChecked, rawChecked, visible⟩ := provenance
          rw [sameName] at path
          refine ⟨declaring, d, i, raw, declaringMember, ?_, member, kind,
            origin, location, isClaim, rawSource, budget, payloadChecked, rawChecked, visible⟩
          simpa only [sourceEq] using
            (ImportPath.via inSource ordered nameMember path)

/-- Accepted source plus selected-module/installed-rule membership suffice for
actual transitive source provenance. The claim-exclusion bit is a conclusion. -/
theorem package_installed_source {cfg fuel text} (p : Package cfg fuel text)
    (m : CheckedModule p.definition.ambient cfg) (selected : m ∈ p.definition.modules)
    (r : LocatedRule p.definition.ambient cfg) (installed : r ∈ m.axioms) :
    InstalledSource p.source fuel m.source.name r :=
  (checkDefinition_history p.accepted).installedSource m selected r installed

/-- No parsed claim is installed as an axiom, including through transitive
imports and repeated paths in a diamond. -/
theorem package_installed_is_axiom {cfg fuel text} (p : Package cfg fuel text)
    (m : CheckedModule p.definition.ambient cfg) (selected : m ∈ p.definition.modules)
    (r : LocatedRule p.definition.ambient cfg) (installed : r ∈ m.axioms) :
    r.isClaim = false := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, kind, _⟩ :=
    package_installed_source p m selected r installed
  exact kind

/-- An installed occurrence retains its actual original checked module, not
merely a free scope field. The witness includes the real earlier checker history,
local-axiom membership, successful module check and a source import path. -/
def OriginatingScope {ambient cfg} (source : Kore.Modules.Definition Raw)
    (fuel : Nat) (moduleName : String) (r : LocatedRule ambient cfg) : Prop :=
  ∃ (earlier : List (CheckedModule ambient cfg)) (origin : CheckedModule ambient cfg),
    CheckedHistory source ambient cfg fuel earlier ∧
    origin.source ∈ source.modules ∧
    checkModule ambient cfg fuel earlier origin.source = some origin ∧
    r ∈ origin.localAxioms ∧ r.payload.declaringScope = origin.scope ∧
    ImportPath source moduleName origin.source.name

/-- Strengthening preserves the original provenance API and adds the originating
checked-module scope witness. No original theorem or hypothesis is weakened. -/
def InstalledSourceWithScope {ambient cfg} (source : Kore.Modules.Definition Raw)
    (fuel : Nat) (moduleName : String) (r : LocatedRule ambient cfg) : Prop :=
  InstalledSource source fuel moduleName r ∧ OriginatingScope source fuel moduleName r

/-- The actual checker history supplies the scope witness in the local case;
real imported parent resolution preserves it through every subsequent import. -/
theorem CheckedHistory.originatingScope {source ambient cfg fuel modules}
    (history : CheckedHistory source ambient cfg fuel modules) :
    ∀ (m : CheckedModule ambient cfg), m ∈ modules →
      ∀ r ∈ m.axioms, OriginatingScope source fuel m.source.name r := by
  induction history with
  | empty => intro m member; simp at member
  | @append earlier original checked prior inSource accepted ih =>
      intro m member r installed
      rcases List.mem_append.mp member with old | newest
      · exact ih m old r installed
      · have same : m = checked := by simpa using newest
        subst m
        have sourceEq := (checkModule_source accepted).1
        change r ∈ checked.localAxioms ++ checked.imports.flatMap Import.axioms at installed
        rcases List.mem_append.mp installed with localEntry | imported
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, scopeEq, _⟩ :=
            checkModule_local_axiom_source accepted localEntry
          have checkedSource : checked.source ∈ source.modules := by
            simpa only [sourceEq] using inSource
          have originalCheck : checkModule ambient cfg fuel earlier checked.source = some checked := by
            simpa only [sourceEq] using accepted
          exact ⟨earlier, checked, prior, checkedSource, originalCheck, localEntry,
            scopeEq, ImportPath.here checkedSource⟩
        · obtain ⟨parent, parentMember, ruleMember⟩ := List.mem_flatMap.mp imported
          obtain ⟨_, _, ⟨names, ordered, parentChecks⟩, _, _, _⟩ := checkModule_source accepted
          obtain ⟨name, nameMember, parentChecked⟩ := mapM_mem _ _ parentChecks parentMember
          obtain ⟨previous, found, sameParent⟩ := Option.map_eq_some_iff.mp parentChecked
          have previousMember : previous ∈ earlier := List.mem_of_find?_eq_some found
          have sameName : previous.source.name = name := by
            simpa using (List.find?_some found)
          rw [← sameParent] at ruleMember
          obtain ⟨precedingModules, origin, prefixHistory, originSource, originCheck,
              originalMember, scopeEq, path⟩ := ih previous previousMember r ruleMember
          rw [sameName] at path
          refine ⟨precedingModules, origin, prefixHistory, originSource, originCheck,
            originalMember, scopeEq, ?_⟩
          simpa only [sourceEq] using
            (ImportPath.via inSource ordered nameMember path)

/-- Package acceptance and selected installed membership expose the actual
originating checked-module scope as well as the original declaration provenance. -/
theorem package_installed_source_with_scope {cfg fuel text} (p : Package cfg fuel text)
    (m : CheckedModule p.definition.ambient cfg) (selected : m ∈ p.definition.modules)
    (r : LocatedRule p.definition.ambient cfg) (installed : r ∈ m.axioms) :
    InstalledSourceWithScope p.source fuel m.source.name r :=
  ⟨package_installed_source p m selected r installed,
    (checkDefinition_history p.accepted).originatingScope m selected r installed⟩

end Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
