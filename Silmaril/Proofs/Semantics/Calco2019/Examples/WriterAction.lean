module

public import Silmaril.Semantics.Calco2019.Examples.Printing.WriterAction.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.WriterAction.Proofs

variable {A M X Y : Type u}

section Action

variable [MulAction (FreeMonoid A) M]

private theorem prefix_nil (p : WriterAction A M X) : prependOutput [] p = p := by
  cases p with
  | inl pair => cases pair; rfl
  | inr m => change Sum.inr ((1 : FreeMonoid A) • m) = Sum.inr m; rw [one_smul]

private theorem prefix_append (word suffix : List A) (p : WriterAction A M X) :
    prependOutput (word ++ suffix) p = prependOutput word (prependOutput suffix p) := by
  cases p with
  | inl pair => cases pair; simp [prependOutput, List.append_assoc]
  | inr m =>
    change Sum.inr ((FreeMonoid.ofList word * FreeMonoid.ofList suffix) • m) = _
    rw [mul_smul]
    rfl

private theorem prefix_bind (word : List A) (p : WriterAction A M X)
    (g : X → WriterAction A M Y) :
    bind (prependOutput word p) g = prependOutput word (bind p g) := by
  cases p with
  | inl pair => obtain ⟨suffix, x⟩ := pair; exact prefix_append word suffix (g x)
  | inr m => rfl

theorem lawful : LawfulMonad (WriterAction A M) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := fun p => by
    cases p with
    | inl pair =>
      obtain ⟨word, x⟩ := pair
      change bind (Sum.inl (word, x)) pureOutput = _
      simp [bind, prependOutput, pureOutput]
    | inr m => rfl)
  (pure_bind := fun x g => prefix_nil (g x))
  (bind_assoc := fun p f g => by
    cases p with
    | inl pair => obtain ⟨word, x⟩ := pair; exact prefix_bind word (f x) g
    | inr m => rfl)

private theorem silent (p : WriterAction A M X) (g : X → WriterAction A M Y) (y : Y)
    (hit : bind p g = .inl ([], y)) :
    ∃ x, p = .inl ([], x) ∧ g x = .inl ([], y) := by
  cases p with
  | inr m => cases hit
  | inl pair =>
    obtain ⟨word, x⟩ := pair
    cases hx : g x with
    | inr m =>
      change prependOutput word (g x) = _ at hit
      rw [hx] at hit
      cases hit
    | inl pair =>
      obtain ⟨suffix, y'⟩ := pair
      change prependOutput word (g x) = _ at hit
      rw [hx] at hit
      have ⟨hw, hy⟩ := Prod.mk.inj (Sum.inl.inj hit)
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hw
      exact ⟨x, rfl, hy ▸ hx⟩

@[expose] def guard : TypeKleisli.Guard (WriterAction A M) where
  holds := Guarded
  trivial {X Y Z} f x z hit := by
    change bind (f x) (fun y => pureOutput (Sum.inl y : Y ⊕ Z)) = .inl ([], .inr z) at hit
    obtain ⟨y, _, hy⟩ := silent _ _ _ hit
    cases hy
  parallel hf hg := by
    intro s
    cases s with
    | inl x => exact hf x
    | inr y => exact hg y
  compose {X Y Z V W} {f g} h hf hg x z hit := by
    change bind (f x) (Sum.elim g h) = .inl ([], .inr z) at hit
    obtain ⟨y | w, hsrc, hdst⟩ := silent _ _ _ hit
    · exact hg y z hdst
    · exact hf x w hsrc

private theorem measure_prefix (len : M → ℕ)
    (hle : ∀ (w : List A) (m : M), len (FreeMonoid.ofList w • m) = w.length + len m)
    (word : List A) (p : WriterAction A M Y) :
    Sum.elim (fun pair => pair.1.length) len (prependOutput word p) =
      word.length + Sum.elim (fun pair => pair.1.length) len p := by
  cases p with
  | inl p => cases p; simp [prependOutput]
  | inr m => exact hle word m

omit [MulAction (FreeMonoid A) M] in
theorem letter_guarded (a : A) : Guarded (letterLoop (M := M) a) := by
  intro x z h
  cases h

theorem no_fixpoint_of_length (a : A) (len : M → ℕ)
    (hle : ∀ (word : List A) (m : M), len (FreeMonoid.ofList word • m) = word.length + len m) :
    ¬ ∃ g : PUnit.{u + 1} → WriterAction A M PUnit.{u + 1},
      ∀ x, bind (letterLoop a x) (Sum.elim pureOutput g) = g x := by
  rintro ⟨g, fix⟩
  have h := congrArg (Sum.elim (fun (p : List A × PUnit.{u + 1}) => p.1.length) len)
    (fix PUnit.unit)
  change Sum.elim (fun p => p.1.length) len (prependOutput [a] (g PUnit.unit)) =
    Sum.elim (fun p => p.1.length) len (g PUnit.unit) at h
  rw [measure_prefix len hle] at h
  simp at h

end Action

section Obstructions

attribute [local instance] emptyAction nonemptyWordAction

theorem ordinary_no_unique (a : A) :
    ¬ (guard (A := A) (M := PEmpty.{u + 1})).HasUniqueFixpoints := by
  intro h
  obtain ⟨g, hg, _⟩ := h (letterLoop a) (letter_guarded a)
  exact no_fixpoint_of_length a PEmpty.elim (fun _ m => m.elim) ⟨g, congrFun hg⟩

theorem words_no_unique (a : A) :
    ¬ (guard (A := A) (M := {w : List A // w ≠ []})).HasUniqueFixpoints := by
  intro h
  obtain ⟨g, hg, _⟩ := h (letterLoop a) (letter_guarded a)
  apply no_fixpoint_of_length a (fun m : {w : List A // w ≠ []} => m.1.length) _ ⟨g, congrFun hg⟩
  intro w m
  change (w ++ m.1).length = w.length + m.1.length
  exact List.length_append

end Obstructions

/-- The plain writer is the empty-action carrier. -/
def ordinaryEquiv (A X : Type u) : WriterAction A PEmpty.{u + 1} X ≃ List A × X where
  toFun := Sum.elim id PEmpty.elim
  invFun := Sum.inl
  left_inv := fun s => by cases s with | inl p => rfl | inr m => exact m.elim
  right_inv _ := rfl

section Streams

attribute [local instance] streamAction

variable {f : X → WriterAction A (ℕ → A) (Y ⊕ X)}

private def body (f : X → WriterAction A (ℕ → A) (Y ⊕ X)) :
    X → Set (Trace A (Y ⊕ X)) := fun x => {f x}

private theorem guarded_body (hf : Guarded f) : TraceGuarded (body f) := by
  intro x z word edge hnil
  subst word
  exact hf x z (Set.mem_singleton_iff.mp edge).symm

private theorem step_body (f : X → WriterAction A (ℕ → A) (Y ⊕ X))
    (g : X → Set (Trace A Y)) (x : X) :
    traceStep (body f) g x = extendTrace (Sum.elim pureTrace g) (f x) := by
  rw [traceStep_eq_bind]
  ext t
  change (∃ s, s = f x ∧ t ∈ extendTrace (Sum.elim pureTrace g) s) ↔ _
  simp

private theorem step_singleton (f : X → WriterAction A (ℕ → A) (Y ⊕ X))
    (g : X → WriterAction A (ℕ → A) Y) :
    traceStep (body f) (fun x => {g x}) =
      fun x => ({bind (f x) (Sum.elim pureOutput g)} : Set (Trace A Y)) := by
  funext x
  rw [step_body]
  cases hx : f x with
  | inr s => rfl
  | inl pair =>
    obtain ⟨w, y | x'⟩ := pair
    · simp [extendTrace, pureTrace, bind, pureOutput, prependOutput, prepend]
    · rw [show extendTrace (Sum.elim pureTrace (fun x => {g x})) (.inl (w, .inr x')) =
        prepend w '' {g x'} from rfl, Set.image_singleton]
      congr 1
      change prepend w (g x') = prependOutput w (g x')
      cases g x' with
      | inl pair => cases pair; rfl
      | inr s => rfl

private theorem finite_unique {x : X} {s t : Trace A Y}
    (h : FiniteTraceRun (body f) x s) (ht : t ∈ greatestTrace (body f) x) : t = s := by
  induction h generalizing t with
  | @returns x word y edge =>
    rw [← greatestTrace_fix, step_body, (Set.mem_singleton_iff.mp edge).symm] at ht
    simpa [extendTrace, pureTrace, prepend] using ht
  | @streams x stream edge =>
    rw [← greatestTrace_fix, step_body, (Set.mem_singleton_iff.mp edge).symm] at ht
    exact Set.mem_singleton_iff.mp ht
  | @next x x' word tail edge _ ih =>
    rw [← greatestTrace_fix, step_body, (Set.mem_singleton_iff.mp edge).symm] at ht
    obtain ⟨s', hs, he⟩ := ht
    exact he.symm.trans (congrArg (prepend word) (ih hs))

private theorem infinite_unique {x : X} (p q : InfiniteTracePath (body f) x) (hf : TraceGuarded (body f)) :
    p.stream hf = q.stream hf := by
  have next (i : ℕ) (h : p.state i = q.state i) :
      p.word i = q.word i ∧ p.state (i + 1) = q.state (i + 1) := by
    have he := (Set.mem_singleton_iff.mp (p.edge i)).trans
      ((congrArg f h).trans (Set.mem_singleton_iff.mp (q.edge i)).symm)
    obtain ⟨hw, hs⟩ := Prod.mk.inj (Sum.inl.inj he)
    exact ⟨hw, Sum.inr.inj hs⟩
  have state (i : ℕ) : p.state i = q.state i := by
    induction i with
    | zero => exact p.start.trans q.start.symm
    | succ i ih => exact (next i ih).2
  have word : p.word = q.word := funext fun i => (next i (state i)).1
  have chunk_congr (w v : ℕ → List A) (hw : ∀ i, 0 < (w i).length)
      (hv : ∀ i, 0 < (v i).length) (eq : w = v) :
      chunkStream w hw 0 = chunkStream v hv 0 := by
    subst v
    rfl
  exact chunk_congr _ _ _ _ word

private theorem member_unique (hf : Guarded f) (x : X) {s t : Trace A Y}
    (hs : s ∈ greatestTrace (body f) x) (ht : t ∈ greatestTrace (body f) x) : s = t := by
  have hg := guarded_body hf
  rcases (greatest_iff hg x s).1 hs with h | ⟨p, rfl⟩
  · exact (finite_unique h ht).symm
  · rcases (greatest_iff hg x t).1 ht with h | ⟨q, rfl⟩
    · exact finite_unique h hs
    · exact congrArg Sum.inr (infinite_unique p q hg)

theorem streams_iterative (A : Type u) :
    (guard (A := A) (M := ℕ → A)).HasUniqueFixpoints := by
  classical
  intro X Y f hf
  change Guarded f at hf
  have hnonempty (x : X) : (greatestTrace (body f) x).Nonempty :=
    greatest_nonempty (guarded_body hf) (fun x => ⟨f x, rfl⟩) x
  let g (x : X) : WriterAction A (ℕ → A) Y := (hnonempty x).choose
  have hit (x : X) : g x ∈ greatestTrace (body f) x := (hnonempty x).choose_spec
  have he : (fun x => ({g x} : Set (Trace A Y))) = greatestTrace (body f) := by
    funext x
    ext t
    exact ⟨fun ht => (Set.mem_singleton_iff.mp ht).symm ▸ hit x,
      fun ht => Set.mem_singleton_iff.mpr (member_unique hf x ht (hit x))⟩
  have solution : traceStep (body f) (fun x => {g x}) = fun x => ({g x} : Set (Trace A Y)) := by
    rw [he, greatestTrace_fix]
  rw [step_singleton] at solution
  refine ⟨g, ?_, fun q hq => ?_⟩
  · funext x
    exact Set.singleton_injective (congrFun solution x)
  · have qs : (fun x => ({q x} : Set (Trace A Y))) ≤ traceStep (body f) (fun x => {q x}) := by
      rw [step_singleton]
      change (fun x => ({q x} : Set (Trace A Y))) ≤ fun x => ({(f >=> Sum.elim pure q) x} : Set _)
      rw [hq]
    funext x
    exact member_unique hf x (le_greatestTrace _ qs x (show q x ∈ {q x} from rfl)) (hit x)

/-- Streams are the final coalgebra for one emitted letter and one next state. -/
theorem streams_final (out : X → A × X) :
    ∃! f : X → ℕ → A, (∀ x, f x 0 = (out x).1) ∧
      ∀ x n, f x (n + 1) = f (out x).2 n := by
  let next : X → X := fun x => (out x).2
  let f (x : X) (n : ℕ) := (out (next^[n] x)).1
  refine ⟨f, ⟨fun _ => rfl, fun x n => ?_⟩, fun g hg => ?_⟩
  · change (out (next^[n + 1] x)).1 = (out (next^[n] (next x))).1
    rw [Function.iterate_succ_apply]
  · funext x n
    induction n generalizing x with
    | zero => exact hg.1 x
    | succ n ih =>
      rw [hg.2]
      change g (next x) n = (out (next^[n + 1] x)).1
      rw [Function.iterate_succ_apply]
      exact ih (next x)

end Streams
section Equivariance

attribute [local instance] singletonAction streamAction nonemptyWordAction

theorem singleton_action_terminal [MulAction (FreeMonoid A) M] :
    ∃! f : M → PUnit.{u + 1}, ∀ (word : FreeMonoid A) x, f (word • x) = word • f x :=
  ⟨fun _ => PUnit.unit, fun _ _ => rfl, fun _ _ => Subsingleton.elim _ _⟩

theorem no_singleton_to_words (a : A) :
    ¬ ∃ f : PUnit.{u + 1} → {w : List A // w ≠ []},
      ∀ (word : FreeMonoid A) x, f (word • x) = word • f x := by
  rintro ⟨f, hf⟩
  have h := congrArg (fun w : {w : List A // w ≠ []} => w.1.length)
    (hf (FreeMonoid.of a) PUnit.unit)
  change (f PUnit.unit).1.length = (a :: (f PUnit.unit).1).length at h
  simp at h

theorem no_singleton_to_streams (a b : A) (hab : a ≠ b) :
    ¬ ∃ f : PUnit.{u + 1} → ℕ → A, ∀ (word : FreeMonoid A) x, f (word • x) = word • f x := by
  rintro ⟨f, hf⟩
  have ha : f PUnit.unit 0 = a := congrFun (hf (FreeMonoid.of a) PUnit.unit) 0
  have hb : f PUnit.unit 0 = b := congrFun (hf (FreeMonoid.of b) PUnit.unit) 0
  exact hab (ha.symm.trans hb)

end Equivariance

end Silmaril.Calco2019.Examples.Printing.WriterAction.Proofs
