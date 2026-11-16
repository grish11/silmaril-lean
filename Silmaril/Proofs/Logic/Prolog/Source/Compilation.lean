module

public import Silmaril.Logic.Prolog.Source.Compilation.Defs

@[expose] public section
namespace Silmaril.Logic.Prolog.Source

/-- Every name in a sentence's binding context has a finite index. -/
theorem findVariable_exists (v : Variable) (names : List Variable) (h : v ∈ names) :
    ∃ i, findVariable? v names = some i := by
  induction names with
  | nil => simp at h
  | cons name rest ih =>
    by_cases hv : v = name
    · subst name
      exact ⟨0, by simp [findVariable?]⟩
    · have hr : v ∈ rest := by simpa [hv] using h
      obtain ⟨i, hi⟩ := ih hr
      exact ⟨i.succ, by simp [findVariable?, hv, hi]⟩

/-- Sequencing a tuple succeeds whenever each component succeeds. -/
theorem sequence_exists {α : Type} (n : Nat) (f : Fin n → Option α)
    (h : ∀ i, ∃ a, f i = some a) : ∃ args, sequence? n f = some args := by
  induction n with
  | zero => exact ⟨Fin.elim0, rfl⟩
  | succ n ih =>
    obtain ⟨first, hf⟩ := h 0
    obtain ⟨rest, hr⟩ := ih (fun i => f i.succ) (fun i => h i.succ)
    exact ⟨Fin.cases first rest, by simp [sequence?, hf, hr]⟩

/-- Resolution is total when the context and finite vocabulary cover the term. -/
theorem resolveTerm_exists (V : Vocabulary) (names : List Variable) (t : NamedTerm)
    (hv : ∀ v ∈ t.variables, v ∈ names)
    (hf : ∀ f ∈ t.functions, f ∈ V.functions) :
    ∃ resolved, resolveTerm? V names t = some resolved := by
  induction t with
  | var v =>
    obtain ⟨i, hi⟩ := findVariable_exists v names (hv v (by simp [NamedTerm.variables]))
    exact ⟨.var i, by simp [resolveTerm?, hi]⟩
  | app name n args ih =>
    have known : (name, n) ∈ V.functions := hf _ (by simp [NamedTerm.functions])
    have ha : ∀ i, ∃ resolved, resolveTerm? V names (args i) = some resolved := by
      intro i
      apply ih i
      · intro v h
        apply hv v
        exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, h⟩
      · intro f h
        apply hf f
        exact List.mem_cons_of_mem _
          (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, h⟩)
    obtain ⟨resolved, hr⟩ := sequence_exists n _ ha
    exact ⟨.app ⟨name, known⟩ resolved, by simp [resolveTerm?, known, hr]⟩

theorem resolveAtom_exists (V : Vocabulary) (names : List Variable) (a : NamedAtom)
    (hv : ∀ v ∈ a.variables, v ∈ names)
    (hf : ∀ f ∈ a.functions, f ∈ V.functions)
    (hp : (a.predicate, a.arity) ∈ V.predicates) :
    ∃ resolved, resolveAtom? V names a = some resolved := by
  have ha : ∀ i, ∃ resolved, resolveTerm? V names (a.arguments i) = some resolved := by
    intro i
    apply resolveTerm_exists
    · intro v h
      exact hv v (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, h⟩)
    · intro f h
      exact hf f (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, h⟩)
  obtain ⟨args, hr⟩ := sequence_exists a.arity _ ha
  exact ⟨⟨a.arity, ⟨a.predicate, hp⟩, args⟩, by simp [resolveAtom?, hp, hr]⟩

/-- A finite list of successful computations has a successful traversal. -/
theorem mapM_exists {α β : Type} (f : α → Option β) (xs : List α)
    (h : ∀ x ∈ xs, ∃ y, f x = some y) : ∃ ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (fun z hz => h z (by simp [hz]))
    exact ⟨y :: ys, by simp [hy, hys]⟩

theorem resolveSentence_exists (V : Vocabulary) (s : NamedSentence)
    (hf : ∀ a ∈ s.atoms, ∀ f ∈ a.functions, f ∈ V.functions)
    (hp : ∀ a ∈ s.atoms, (a.predicate, a.arity) ∈ V.predicates) :
    ∃ resolved, resolveSentence? V s = some resolved := by
  have ha : ∀ a ∈ s.atoms, ∃ resolved, resolveAtom? V s.variables a = some resolved := by
    intro a h
    apply resolveAtom_exists
    · intro v hv
      simp only [NamedSentence.variables, List.mem_eraseDups]
      exact List.mem_flatMap.mpr ⟨a, h, hv⟩
    · exact hf a h
    · exact hp a h
  cases s with
  | clause head body =>
    obtain ⟨head', hh⟩ := ha head (by simp [NamedSentence.atoms])
    obtain ⟨body', hb⟩ := mapM_exists _ body (fun a h => ha a (by simp [NamedSentence.atoms, h]))
    exact ⟨.clause ⟨_, head', body'⟩, by simp [resolveSentence?, hh, hb]⟩
  | query goals =>
    obtain ⟨goals', hg⟩ := mapM_exists _ goals (fun a h => ha a h)
    exact ⟨.query ⟨_, goals'⟩, by simp [resolveSentence?, hg]⟩

/-- The vocabulary inferred from the complete input suffices for every sentence. -/
theorem resolveProgram_exists (sentences : List NamedSentence) :
    ∃ resolved, resolveProgram? sentences = some resolved := by
  have hs : ∀ s ∈ sentences, ∃ resolved,
      resolveSentence? (inferVocabulary sentences) s = some resolved := by
    intro s hs
    apply resolveSentence_exists
    · intro a ha f hf
      simp only [inferVocabulary, List.mem_eraseDups]
      exact List.mem_flatMap.mpr ⟨s, hs, List.mem_flatMap.mpr ⟨a, ha, hf⟩⟩
    · intro a ha
      simp only [inferVocabulary, List.mem_eraseDups]
      exact List.mem_flatMap.mpr ⟨s, hs, List.mem_map.mpr ⟨a, ha, rfl⟩⟩
  obtain ⟨resolved, hr⟩ := mapM_exists _ sentences hs
  exact ⟨⟨inferVocabulary sentences, resolved⟩, by simp [resolveProgram?, hr]⟩

/-- Resolution never changes a variable's source name. -/
theorem findVariable_get (v : Variable) (names : List Variable) (i : Fin names.length)
    (h : findVariable? v names = some i) : names.get i = v := by
  induction names with
  | nil => exact Fin.elim0 i
  | cons name rest ih =>
    by_cases hv : v = name
    · simp [findVariable?, hv] at h
      subst i
      exact hv.symm
    · cases hr : findVariable? v rest with
      | none => simp [findVariable?, hv, hr] at h
      | some j =>
        simp [findVariable?, hv, hr] at h
        subst i
        exact ih j hr

/-- Each component of a successful finite traversal is the corresponding input. -/
theorem sequence_component {α : Type} (n : Nat) (f : Fin n → Option α)
    (args : Fin n → α) (h : sequence? n f = some args) :
    ∀ i, f i = some (args i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    cases hf : f 0 with
    | none => simp [sequence?, hf] at h
    | some first =>
      cases hr : sequence? n (fun i => f i.succ) with
      | none => simp [sequence?, hf, hr] at h
      | some rest =>
        simp [sequence?, hf, hr] at h
        subst args
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hf
        · exact ih _ rest hr j

/-- Successful resolution preserves the entire named source tree, including
arity, symbol identity, repeated names and argument order. -/
theorem resolveTerm_erase (V : Vocabulary) (names : List Variable) (t : NamedTerm)
    (resolved : Term V names.length) (h : resolveTerm? V names t = some resolved) :
    resolved.erase names = t := by
  induction t generalizing resolved with
  | var v =>
    cases hi : findVariable? v names with
    | none => simp [resolveTerm?, hi] at h
    | some i =>
      simp [resolveTerm?, hi] at h
      subst resolved
      exact congrArg NamedTerm.var (findVariable_get v names i hi)
  | app name n args ih =>
    by_cases known : (name, n) ∈ V.functions
    · cases hr : sequence? n (fun i => resolveTerm? V names (args i)) with
      | none => simp [resolveTerm?, known, hr] at h
      | some terms =>
        simp [resolveTerm?, known, hr] at h
        subst resolved
        apply congrArg (NamedTerm.app name n)
        funext i
        exact ih i (terms i) (sequence_component n _ terms hr i)
    · simp [resolveTerm?, known] at h

theorem resolveAtom_erase (V : Vocabulary) (names : List Variable) (a : NamedAtom)
    (resolved : Atom V names.length) (h : resolveAtom? V names a = some resolved) :
    resolved.erase names = a := by
  by_cases known : (a.predicate, a.arity) ∈ V.predicates
  · cases hr : sequence? a.arity (fun i => resolveTerm? V names (a.arguments i)) with
    | none => simp [resolveAtom?, known, hr] at h
    | some terms =>
      simp [resolveAtom?, known, hr] at h
      subst resolved
      have ht : (fun i => (terms i).erase names) = a.arguments := by
        funext i
        exact resolveTerm_erase V names (a.arguments i) (terms i)
          (sequence_component a.arity _ terms hr i)
      cases a
      simp only [Atom.erase, ht]
  · simp [resolveAtom?, known] at h

/-- A successful traversal is faithful when each successful component is. -/
theorem mapM_erase {α β : Type} (f : α → Option β) (g : β → α) (xs : List α)
    (ys : List β) (h : xs.mapM f = some ys)
    (hg : ∀ x y, f x = some y → g y = x) : ys.map g = xs := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; rfl
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [hx] at h
    | some y =>
      cases hr : xs.mapM f with
      | none => simp [hx, hr] at h
      | some rest =>
        simp [hx, hr] at h
        subst ys
        simp only [List.map_cons, hg x y hx, ih rest hr]

/-- Successful sentence resolution preserves the whole source tree and binds
exactly its original sentence-local named/anonymous context. -/
theorem resolveSentence_erase (V : Vocabulary) (s : NamedSentence) (resolved : Sentence V)
    (h : resolveSentence? V s = some resolved) :
    resolved.erase = s ∧ resolved.context = s.variables := by
  cases s with
  | clause head body =>
    cases hh : resolveAtom? V (NamedSentence.clause head body).variables head with
    | none => simp [resolveSentence?, hh] at h
    | some head' =>
      cases hb : body.mapM (resolveAtom? V (NamedSentence.clause head body).variables) with
      | none => simp [resolveSentence?, hh, hb] at h
      | some body' =>
        simp [resolveSentence?, hh, hb] at h
        subst resolved
        have he := resolveAtom_erase V _ head head' hh
        have be := mapM_erase _ (Atom.erase _) body body' hb (resolveAtom_erase V _)
        exact ⟨by simp only [Sentence.erase, he, be], rfl⟩
  | query goals =>
    cases hg : goals.mapM (resolveAtom? V (NamedSentence.query goals).variables) with
    | none => simp [resolveSentence?, hg] at h
    | some goals' =>
      simp [resolveSentence?, hg] at h
      subst resolved
      have ge := mapM_erase _ (Atom.erase _) goals goals' hg (resolveAtom_erase V _)
      exact ⟨by simp only [Sentence.erase, ge], rfl⟩

theorem resolveProgram_erase (sentences : List NamedSentence) (resolved : ResolvedProgram)
    (h : resolveProgram? sentences = some resolved) :
    resolved.sentences.map Sentence.erase = sentences := by
  cases hr : sentences.mapM (resolveSentence? (inferVocabulary sentences)) with
  | none => simp [resolveProgram?, hr] at h
  | some ss =>
    simp [resolveProgram?, hr] at h
    subst resolved
    exact mapM_erase _ Sentence.erase sentences ss hr
      (fun s r hs => (resolveSentence_erase _ s r hs).1)

end Silmaril.Logic.Prolog.Source
