module

public import Silmaril.Logic.ACL2.Books.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.ACL2.Books

open CategoryTheory Silmaril.Logic.ACL2

variable {P Q : Presentation} {W V U : World} {name : Name} {n : Nat}

theorem equation_map {S T : Signature} (σ : S ⟶ T) {k : Nat}
    (f : S.Symbol k) (t : Term S k) :
    (definitionEquation f t).map σ = definitionEquation (σ.symbol f) (t.map σ) := rfl

theorem equations_map (f : P ⟶ Q) : Set.MapsTo (Sentence.map f.signature) P.equations Q.equations := by
  rintro _ ⟨k, name, t, ht, rfl⟩
  exact ⟨k, f.signature.symbol name, t.map f.signature, f.body name t ht, equation_map ..⟩

theorem define_body_new (P : Presentation) (fresh : P.signature.arity name = none)
    (t : Term P.signature n) :
    (P.define fresh t).body (P.signature.addSymbol name n) =
      some (t.map (Signature.addInclusion fresh n)) := by
  simp [Presentation.define, Signature.addSymbol]

theorem define_equations (P : Presentation) (fresh : P.signature.arity name = none)
    (t : Term P.signature n) :
    (P.define fresh t).equations =
      insert (definitionEquation (P.signature.addSymbol name n)
        (t.map (Signature.addInclusion fresh n)))
        (Sentence.map (Signature.addInclusion fresh n) '' P.equations) := by
  ext p
  constructor
  · rintro ⟨k, f, u, hu, rfl⟩
    by_cases h : f.val = name
    · have hk : n = k := Option.some.inj (by simpa [Presentation.define, Signature.add, h] using f.property)
      subst k
      have hf : f = P.signature.addSymbol name n := Subtype.ext h
      subst f
      rw [define_body_new] at hu
      cases hu
      exact Set.mem_insert _ _
    · have hf : P.signature.arity f.val = some k := by
        simpa [Presentation.define, Signature.add, h] using f.property
      let old : P.signature.Symbol k := ⟨f.val, hf⟩
      have hsame : (Signature.addInclusion fresh n).symbol old = f := Subtype.ext rfl
      rw [← hsame, Presentation.define_body_old] at hu
      obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.mp hu
      exact Set.mem_insert_of_mem _ ⟨_, ⟨k, old, body, hbody, rfl⟩, equation_map ..⟩
  · rintro (rfl | ⟨q, hq, rfl⟩)
    · exact ⟨n, _, _, define_body_new P fresh t, rfl⟩
    · exact equations_map (P.defineHom fresh t) hq

theorem presentation_map_derives (f : P ⟶ Q) {Γ : Set (Sentence P.signature)}
    {p : Sentence P.signature} (h : P.Derives Γ p) :
    Q.Derives (Sentence.map f.signature '' Γ) (p.map f.signature) := by
  apply (h.map f.signature).weaken
  rintro _ ⟨q, hq, rfl⟩
  exact hq.elim (fun hq => Or.inl (equations_map f hq)) (fun hq => Or.inr ⟨q, hq, rfl⟩)

theorem theory_map (e : W.Extension V) :
    Set.MapsTo (Sentence.map e.presentation.signature) W.theory V.theory := by
  intro p hp
  rcases hp with hd | ⟨f, hf⟩
  · exact Or.inl (equations_map e.presentation hd)
  · exact Or.inr ⟨f, e.theoremAt f p hf⟩

theorem models_reduct (e : W.Extension V) {M : Model V.signature} (hM : V.Models M) :
    W.Models (M.reduct e.presentation.signature) :=
  fun p hp => (p.holds_map _ M).mp (hM _ (theory_map e hp))

theorem world_provable_map (e : W.Extension V) {p : Sentence W.signature} (h : W.Provable p) :
    V.Provable (p.map e.presentation.signature) :=
  (h.map _).weaken fun _ ⟨_, hp, he⟩ => he ▸ theory_map e hp

theorem event_checked (e : Event W V) (hW : W.Checked) : V.Checked := by
  cases e with
  | @defun _ fresh n t =>
    rintro p ⟨f, hf⟩
    let σ := Signature.addInclusion fresh.1 n
    change (W.theoremAt f).map (Sentence.map σ) = some p at hf
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hf
    exact ((hW q ⟨f, hq⟩).map σ).weaken
      (Set.image_subset_iff.mpr (equations_map (W.presentation.defineHom fresh.1 t)))
  | @defthm name _ stated certificate =>
    rintro p ⟨f, hf⟩
    by_cases h : f = name
    · subst f
      have he : stated = p := Option.some.inj (by simpa [World.addTheorem] using hf)
      subst p
      exact hW.discharge certificate
    · exact hW p ⟨f, by simpa [World.addTheorem, h] using hf⟩

theorem book_checked (b : Book W V) (hW : W.Checked) : V.Checked := by
  induction b with
  | nil => exact hW
  | cons e _ ih => exact ih (event_checked e hW)

theorem valid_bare (S : Signature) : (World.bare S).Valid := by
  intro M hM p hp
  rcases hp with hd | ⟨_, ht⟩
  · exact hM p hd
  · cases ht

theorem event_valid (e : Event W V) (hW : W.Valid) : V.Valid := by
  cases e with
  | @defun _ fresh n t =>
    intro M hM p hp
    let σ := Signature.addInclusion fresh.1 n
    have old : W.presentation.Models (M.reduct σ) := fun q hq =>
      (q.holds_map σ M).mp (hM _ (equations_map (W.presentation.defineHom fresh.1 t) hq))
    rcases hp with hd | ⟨f, hf⟩
    · exact hM p hd
    · change (W.theoremAt f).map (Sentence.map σ) = some p at hf
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hf
      exact (q.holds_map σ M).mpr (hW _ old q (Or.inr ⟨f, hq⟩))
  | @defthm name fresh stated certificate =>
    intro M hM p hp
    rcases hp with hd | ⟨f, hf⟩
    · exact hM p hd
    · by_cases h : f = name
      · subst f
        have he : stated = p := Option.some.inj (by simpa [World.addTheorem] using hf)
        subst p
        exact certificate.sound M (hW M hM)
      · exact hW M hM p (Or.inr ⟨f, by simpa [World.addTheorem, h] using hf⟩)

theorem book_valid (b : Book W V) (hW : W.Valid) : V.Valid := by
  induction b with
  | nil => exact hW
  | cons e _ ih => exact ih (event_valid e hW)

/-- Extend denotations with a single new function defined by evaluation in the old model. -/
def expandDefinition (M : Model P.signature) (_fresh : P.signature.arity name = none)
    (t : Term P.signature n) : Model (P.signature.add name n) where
  primitives := M.primitives
  interpret {k} f args :=
    if h : f.val = name then
      have arity : n = k := Option.some.inj (by simpa [Signature.add, h] using f.property)
      t.eval M (arity.symm ▸ args)
    else
      M.interpret ⟨f.val, by simpa [Signature.add, h] using f.property⟩ args

theorem expand_interpret (M : Model P.signature) (fresh : P.signature.arity name = none)
    (t : Term P.signature n) :
    @((expandDefinition M fresh t).reduct (Signature.addInclusion fresh n)).interpret =
      @M.interpret := by
  funext k f args
  simp [Model.reduct, expandDefinition, Signature.Hom.symbol, Signature.ne_of_fresh fresh f]

theorem expand_reduct (M : Model P.signature) (fresh : P.signature.arity name = none)
    (t : Term P.signature n) :
    (expandDefinition M fresh t).reduct (Signature.addInclusion fresh n) = M :=
  congrArg (fun f => Model.mk M.primitives f) (expand_interpret M fresh t)

theorem expand_equation (M : Model P.signature) (fresh : P.signature.arity name = none)
    (t : Term P.signature n) :
    (definitionEquation (P.signature.addSymbol name n) (t.map (Signature.addInclusion fresh n))).Holds
      (expandDefinition M fresh t) := by
  apply (Sentence.holds_eq ..).mpr
  intro env
  let evaluate (f : ∀ k, P.signature.Symbol k → (Fin k → M.primitives.Value) → M.primitives.Value) :
      M.primitives.Value := t.eval (Model.mk M.primitives (fun {k} => f k)) env
  have he := congrArg evaluate (expand_interpret M fresh t)
  change t.eval ((expandDefinition M fresh t).reduct (Signature.addInclusion fresh n)) env =
    t.eval M env at he
  rw [Term.eval_map, he]
  simp [Term.eval, expandDefinition, Signature.addSymbol]

theorem event_expand (e : Event W V) (M : Model W.signature) (hM : W.Models M) :
    ∃ N : Model V.signature, V.Models N ∧ N.reduct e.extension.presentation.signature = M := by
  cases e with
  | @defun _ fresh n t =>
    refine ⟨expandDefinition M fresh.1 t, ?_, expand_reduct M fresh.1 t⟩
    intro p hp
    have fromOld (q : Sentence W.signature) (hq : q ∈ W.theory) :
        (q.map (Signature.addInclusion fresh.1 _)).Holds (expandDefinition M fresh.1 t) := by
      apply (q.holds_map ..).mpr
      rw [expand_reduct]
      exact hM q hq
    rcases hp with hd | ⟨f, hf⟩
    · change p ∈ (W.presentation.define fresh.1 t).equations at hd
      rw [define_equations] at hd
      rcases hd with rfl | ⟨q, hq, rfl⟩
      · exact expand_equation M fresh.1 t
      · exact fromOld q (Or.inl hq)
    · change (W.theoremAt f).map _ = some p at hf
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hf
      exact fromOld q (Or.inr ⟨f, hq⟩)
  | @defthm name fresh stated certificate =>
    refine ⟨M, ?_, rfl⟩
    intro p hp
    rcases hp with hd | ⟨f, hf⟩
    · exact hM p (Or.inl hd)
    · by_cases h : f = name
      · subst f
        have he : stated = p := Option.some.inj (by simpa [World.addTheorem] using hf)
        subst p
        exact certificate.sound M hM
      · exact hM p (Or.inr ⟨f, by simpa [World.addTheorem, h] using hf⟩)

theorem book_expand (b : Book W V) (M : Model W.signature) (hM : W.Models M) :
    ∃ N : Model V.signature, V.Models N ∧ N.reduct b.extension.presentation.signature = M := by
  induction b with
  | nil => exact ⟨M, hM, rfl⟩
  | cons e tail ih =>
    obtain ⟨N, hN, hred⟩ := event_expand e M hM
    obtain ⟨O, hO, hred'⟩ := ih N hN
    exact ⟨O, hO, (congrArg (Model.reduct e.extension.presentation.signature) hred').trans hred⟩

theorem book_entails_iff (b : Book W V) (p : Sentence W.signature) :
    V.Entails (p.map b.extension.presentation.signature) ↔ W.Entails p := by
  constructor
  · intro h M hM
    obtain ⟨N, hN, hred⟩ := book_expand b M hM
    exact hred ▸ (p.holds_map _ N).mp (h N hN)
  · intro h N hN
    exact (p.holds_map _ N).mpr (h _ (models_reduct b.extension hN))

end Silmaril.Proofs.Logic.ACL2.Books
