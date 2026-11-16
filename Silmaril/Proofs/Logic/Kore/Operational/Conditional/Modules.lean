module

public import Silmaril.Logic.Kore.Operational.Conditional.Modules.Defs
public import Silmaril.Logic.Kore.Operational.Conditional.Execution.Thms

@[expose] public section
namespace Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules
open Silmaril.Logic.Kore.Operational (Declaration)
open Silmaril.Logic.Kore.Operational.Conditional
open Silmaril.Logic.Kore.Operational.Conditional.Modules

theorem route_sound {modules : List SourceModule} {route : Route}
    (h : route.Valid modules) : ImportChain modules route.start route.finish := by
  induction route with
  | «local» name => exact .local h
  | via name tail ih => exact .importStep h.1 (ih h.2)

/-- Certificate validation bridges executable membership to independent source
import paths in both directions; generated cache membership is not the spec. -/
theorem seen_iff_chain {modules : List SourceModule} {routes : List Route}
    (h : CertificateValid modules routes) (source origin : String) :
    Seen routes source origin ↔ ImportChain modules source origin := by
  constructor
  · rintro ⟨route, hr, hs, he⟩
    have path := route_sound (h.1 route hr)
    simpa only [hs, he] using path
  · intro path
    induction path with
    | «local» present =>
      rcases present with ⟨m, hm, rfl⟩
      exact h.2.1 m hm
    | @importStep source imported origin edge _ ih =>
      rcases edge with ⟨m, hm, rfl, i, hi, rfl⟩
      rcases ih with ⟨route, hr, hs, he⟩
      have result := h.2.2 m hm i hi route hr hs
      simpa only [he] using result

theorem visible_iff (p : CheckedDefinition) (target : String) (m : SourceModule) :
    m ∈ p.visible target ↔
      m ∈ p.source.modules ∧ ImportChain p.source.modules target m.name := by
  simp only [CheckedDefinition.visible, List.mem_filter, decide_eq_true_eq]
  rw [seen_iff_chain p.certificate]

theorem declaration_iff (p : CheckedDefinition) (target : String) (d : Declaration) :
    d ∈ p.declarations target ↔
      ∃ m ∈ p.source.modules,
        ImportChain p.source.modules target m.name ∧ d ∈ m.declarations := by
  simp only [CheckedDefinition.declarations, List.mem_flatMap, visible_iff]
  constructor
  · rintro ⟨m, ⟨hm, hc⟩, hd⟩
    exact ⟨m, hm, hc, hd⟩
  · rintro ⟨m, hm, hc, hd⟩
    exact ⟨m, ⟨hm, hc⟩, hd⟩

theorem declarationRule_iff (d : Declaration) (r : Rule) :
    declarationRule d = some r ↔
      d.kind = .ruleAxiom ∧ ∃ Γ, elaborate d = some (Γ, r) := by
  unfold declarationRule
  split
  · rename_i hk
    simp only [hk, true_and, Option.map_eq_some_iff]
    constructor
    · rintro ⟨⟨Γ, r'⟩, h, hr⟩
      cases hr
      exact ⟨Γ, h⟩
    · rintro ⟨Γ, h⟩
      exact ⟨(Γ, r), h, rfl⟩
  · rename_i hk
    simp [hk]

theorem axiom_iff (p : CheckedDefinition) (target : String) (r : Rule) :
    r ∈ p.axioms target ↔
      ∃ m ∈ p.source.modules,
        ImportChain p.source.modules target m.name ∧
        ∃ d ∈ m.declarations,
          d.kind = .ruleAxiom ∧ ∃ Γ, elaborate d = some (Γ, r) := by
  simp only [CheckedDefinition.axioms, List.mem_filterMap,
    declaration_iff, declarationRule_iff]
  constructor
  · rintro ⟨d, ⟨m, hm, hc, hd⟩, hk, Γ, he⟩
    exact ⟨m, hm, hc, d, hd, hk, Γ, he⟩
  · rintro ⟨m, hm, hc, d, hd, hk, Γ, he⟩
    exact ⟨d, ⟨m, hm, hc, hd⟩, hk, Γ, he⟩

theorem all_declarations_checked (p : CheckedDefinition) {m : SourceModule}
    (hm : m ∈ p.source.modules) {d : Declaration} (hd : d ∈ m.declarations) :
    ∃ pair, elaborate d = some pair := by
  have he := (p.profile.2 m hm).2.2 d hd
  exact Option.isSome_iff_exists.mp he

theorem step_iff_source (p : CheckedDefinition) (target : String) (c d : Config) :
    Step (p.axioms target) c d ↔ SourceStep p.source target c d := by
  constructor
  · intro h
    cases h with
    | rule r hr v coherent enabled =>
      rcases (axiom_iff p target r).1 hr with
        ⟨m, hm, hc, declaration, hd, hk, Γ, he⟩
      exact .rule m hm hc declaration hd hk Γ r he v coherent enabled
  · intro h
    cases h with
    | rule m hm hc declaration hd hk Γ r he v coherent enabled =>
      exact .rule r ((axiom_iff p target r).2
        ⟨m, hm, hc, declaration, hd, hk, Γ, he⟩) v coherent enabled

/-- Module execution is exact for every ordinary Config, including all tails,
signed values, counters, deadlocks and overlapping enabled rules. -/
theorem successors_iff (p : CheckedDefinition) (target : String) (c d : Config) :
    d ∈ Execution.successors (p.axioms target) c ↔ SourceStep p.source target c d := by
  rw [Execution.mem_successors, step_iff_source]

private theorem present_mono {xs ys : List SourceModule}
    (hxy : ∀ m ∈ xs, m ∈ ys) {name : String} (h : Present xs name) :
    Present ys name := by
  rcases h with ⟨m, hm, hn⟩
  exact ⟨m, hxy m hm, hn⟩

private theorem edge_mono {xs ys : List SourceModule}
    (hxy : ∀ m ∈ xs, m ∈ ys) {a b : String} (h : Edge xs a b) :
    Edge ys a b := by
  rcases h with ⟨m, hm, hn, i, hi, he⟩
  exact ⟨m, hxy m hm, hn, i, hi, he⟩

private theorem valid_mono {xs ys : List SourceModule}
    (hxy : ∀ m ∈ xs, m ∈ ys) {route : Route} (h : route.Valid xs) :
    route.Valid ys := by
  induction route with
  | «local» name => exact present_mono hxy h
  | via name tail ih => exact ⟨edge_mono hxy h.1, ih h.2⟩

private theorem seen_mono {xs ys : List Route}
    (hxy : ∀ route ∈ xs, route ∈ ys) {a b : String} (h : Seen xs a b) :
    Seen ys a b := by
  rcases h with ⟨route, hr, hs, he⟩
  exact ⟨route, hxy route hr, hs, he⟩

private def Closed (modules : List SourceModule) : Prop :=
  ∀ m ∈ modules, ∀ i ∈ m.imports, Present modules i.name

private def addedRoutes (routes : List Route) (m : SourceModule) : List Route :=
  Route.local m.name :: m.imports.flatMap (fun i =>
    (routes.filter (fun route => route.start == i.name)).map (Route.via m.name))

private theorem mem_added (routes : List Route) (m : SourceModule) (route : Route) :
    route ∈ addedRoutes routes m ↔
      route = Route.local m.name ∨
        ∃ i ∈ m.imports, ∃ tail ∈ routes,
          tail.start = i.name ∧ route = Route.via m.name tail := by
  simp only [addedRoutes, List.mem_cons, List.mem_flatMap, List.mem_map,
    List.mem_filter, beq_iff_eq]
  constructor
  · rintro (h | ⟨i, hi, tail, ⟨ht, hs⟩, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, tail, ht, hs, he.symm⟩
  · rintro (h | ⟨i, hi, tail, ht, hs, he⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, tail, ⟨ht, hs⟩, he.symm⟩

private theorem added_start {routes : List Route} {m : SourceModule} {route : Route}
    (h : route ∈ addedRoutes routes m) : route.start = m.name := by
  rcases (mem_added routes m route).1 h with h | ⟨_, _, _, _, _, h⟩
  · subst route
    rfl
  · subst route
    rfl

private theorem certificate_extend {done : List SourceModule} {routes : List Route}
    (valid : CertificateValid done routes) (closed : Closed done)
    (m : SourceModule) (fresh : ¬ Present done m.name)
    (imports : ∀ i ∈ m.imports, Present done i.name) :
    CertificateValid (done ++ [m]) (routes ++ addedRoutes routes m) := by
  have old_modules : ∀ q ∈ done, q ∈ done ++ [m] := by
    intro q hq
    exact List.mem_append_left _ hq
  have old_routes : ∀ route ∈ routes, route ∈ routes ++ addedRoutes routes m := by
    intro route hr
    exact List.mem_append_left _ hr
  have new_routes : ∀ route ∈ addedRoutes routes m,
      route ∈ routes ++ addedRoutes routes m := by
    intro route hr
    exact List.mem_append_right _ hr
  have here : Route.local m.name ∈ addedRoutes routes m :=
    (mem_added routes m _).2 (Or.inl rfl)
  have contradiction {route : Route} {name : String}
      (hr : route ∈ addedRoutes routes m) (hs : route.start = name)
      (hp : Present done name) : False := by
    have he : m.name = name := (added_start hr).symm.trans hs
    apply fresh
    simpa only [he] using hp
  refine ⟨?_, ?_, ?_⟩
  · intro route hr
    rcases List.mem_append.1 hr with hr | hr
    · exact valid_mono old_modules (valid.1 route hr)
    · rcases (mem_added routes m route).1 hr with hr | ⟨i, hi, tail, ht, hs, hr⟩
      · subst route
        exact ⟨m, by simp, rfl⟩
      · subst route
        refine ⟨?_, valid_mono old_modules (valid.1 tail ht)⟩
        exact ⟨m, by simp, rfl, i, hi, hs.symm⟩
  · intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact seen_mono old_routes (valid.2.1 q hq)
    · have hqm : q = m := List.mem_singleton.1 hq
      subst q
      exact ⟨Route.local m.name, new_routes _ here, rfl, rfl⟩
  · intro q hq i hi route hr hs
    rcases List.mem_append.1 hq with hq | hq
    · rcases List.mem_append.1 hr with hr | hr
      · exact seen_mono old_routes (valid.2.2 q hq i hi route hr hs)
      · exact False.elim (contradiction hr hs (closed q hq i hi))
    · have hqm : q = m := List.mem_singleton.1 hq
      subst q
      rcases List.mem_append.1 hr with hr | hr
      · have added : Route.via m.name route ∈ addedRoutes routes m :=
          (mem_added routes m _).2 (Or.inr ⟨i, hi, route, hr, hs, rfl⟩)
        exact ⟨Route.via m.name route, new_routes _ added, rfl, rfl⟩
      · exact False.elim (contradiction hr hs (imports i hi))

private theorem closed_extend {done : List SourceModule} (closed : Closed done)
    (m : SourceModule) (imports : ∀ i ∈ m.imports, Present done i.name) :
    Closed (done ++ [m]) := by
  intro q hq i hi
  have old_modules : ∀ q ∈ done, q ∈ done ++ [m] := by
    intro q hq
    exact List.mem_append_left _ hq
  rcases List.mem_append.1 hq with hq | hq
  · exact present_mono old_modules (closed q hq i hi)
  · have hqm : q = m := List.mem_singleton.1 hq
    subst q
    exact present_mono old_modules (imports i hi)

private theorem resolveFrom_complete (remaining : List SourceModule) :
    ∀ (done : List SourceModule) (seen : List String) (routes : List Route),
      (∀ name, name ∈ seen ↔ Present done name) →
      CertificateValid done routes → Closed done → OrderedFrom seen remaining →
      CertificateValid (done ++ remaining) (resolveFrom routes remaining) := by
  induction remaining with
  | nil =>
    intro done seen routes _ valid _ _
    simpa only [List.append_nil, resolveFrom] using valid
  | cons m rest ih =>
    intro done seen routes names valid closed ordered
    have fresh : ¬ Present done m.name := by
      intro present
      exact ordered.1 ((names m.name).2 present)
    have imports : ∀ i ∈ m.imports, Present done i.name := by
      intro i hi
      exact (names i.name).1 (ordered.2.1 i hi)
    have names' : ∀ name, name ∈ m.name :: seen ↔ Present (done ++ [m]) name := by
      intro name
      rw [List.mem_cons]
      unfold Present
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (he | hn)
        · exact ⟨m, Or.inr rfl, he.symm⟩
        · rcases (names name).1 hn with ⟨q, hq, hname⟩
          exact ⟨q, Or.inl hq, hname⟩
      · rintro ⟨q, hq | hq, hname⟩
        · exact Or.inr ((names name).2 ⟨q, hq, hname⟩)
        · subst q
          exact Or.inl hname.symm
    have result := ih (done ++ [m]) (m.name :: seen)
      (routes ++ addedRoutes routes m) names'
      (certificate_extend valid closed m fresh imports)
      (closed_extend closed m imports) ordered.2.2
    simpa only [List.append_assoc, List.singleton_append, resolveFrom, addedRoutes] using result

/-- Every structurally valid earlier-import module graph makes the generated
witness certificate pass. The finite validator introduces no acceptance caveat. -/
theorem resolve_complete :
    ∀ modules : List SourceModule, OrderedFrom [] modules →
      CertificateValid modules (resolve modules) := by
  intro modules ordered
  have valid : CertificateValid [] [] := by
    constructor
    · intro route h
      simp at h
    constructor
    · intro m h
      simp at h
    · intro m h
      simp at h
  have closed : Closed [] := by
    intro m h
    simp at h
  have names : ∀ name : String, name ∈ ([] : List String) ↔ Present [] name := by
    intro name
    simp [Present]
  simpa only [List.nil_append, resolve] using
    resolveFrom_complete modules [] [] [] names valid closed ordered

end Silmaril.Proofs.Logic.Kore.Operational.Conditional.Modules
