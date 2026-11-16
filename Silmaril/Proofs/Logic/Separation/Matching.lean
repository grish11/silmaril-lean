module

public import Silmaril.Logic.Separation.Matching.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation
open CategoryTheory Silmaril.Logic.Institution
variable {A : Signature}

private theorem pair_map {α β : Type} (f : α → β) (a b : α) :
    (fun i : Fin 2 => f (Fin.cases a (fun _ => b) i)) = Fin.cases (f a) (fun _ => f b) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem nullary_denote (M : Model A) (op : (matchingSignature A).operations 0 (fun _ => ()) ()) :
    (matchingModel M).denote (fun i : Fin 0 => i.elim0) (.app op (fun i => i.elim0) : MatchingAssertion A) =
      (matchingModel M).operation op (fun i => i.elim0) := by
  ext h
  constructor
  · rintro ⟨args, _, hh⟩
    have he : args = fun i => i.elim0 := funext fun i => i.elim0
    exact he ▸ hh
  · intro hh
    exact ⟨(fun i => i.elim0), (fun i => i.elim0), hh⟩

theorem join_application (M : Model A) (P Q : Set M.resource.carrier) :
    Matching.FixedPoint.application (matchingModel M) .join (Fin.cases P (fun _ => Q)) =
      M.resource.sep P Q := by
  ext h
  constructor
  · rintro ⟨args, ha, hj⟩
    exact ⟨args 0, args 1, hj, ha 0, ha 1⟩
  · rintro ⟨a,b,hj,ha,hb⟩
    refine ⟨(Fin.cases a (fun _ : Fin 1 => b) : Fin 2 → M.resource.carrier), ?_, ?_⟩
    · intro i
      exact Fin.cases ha (fun _ => hb) i
    · exact hj

theorem extension_negative (M : Model A) (P Q : Set M.resource.carrier) :
    (Matching.FixedPoint.application (matchingModel M) .extension (Fin.cases P (fun _ => Qᶜ)))ᶜ =
      M.resource.wand P Q := by
  classical
  ext h
  constructor
  · intro hn a b hj ha
    by_contra hb
    apply hn
    refine ⟨(Fin.cases a (fun _ : Fin 1 => b) : Fin 2 → M.resource.carrier), ?_, ?_⟩
    · intro i; exact Fin.cases ha (fun _ => hb) i
    · exact hj
  · intro hw ⟨args, ha, hj⟩
    exact ha 1 (hw _ _ hj (ha 0))

theorem extension_dual (M : Model A) (P Q : Set M.resource.carrier) :
    Matching.FixedPoint.dualApplication (matchingModel M) .extension (Fin.cases Pᶜ (fun _ => Q)) =
      M.resource.wand P Q := by
  have he : (fun i : Fin 2 => (Fin.cases Pᶜ (fun _ => Q) i)ᶜ) = Fin.cases P (fun _ => Qᶜ) := by
    funext i
    exact Fin.cases (compl_compl P) (fun _ => rfl) i
  unfold Matching.FixedPoint.dualApplication
  rw [he]
  exact extension_negative M P Q

theorem compileBase_denote (M : Model A) (p : Assertion A) :
    (matchingModel M).denote (fun i : Fin 0 => i.elim0) (compileBase p) = p.denote M := by
  induction p with
  | atom a => exact nullary_denote M (.atom a)
  | emp => exact nullary_denote M .emp
  | neg p hp => exact congrArg Set.compl hp
  | conj p q hp hq => exact congrArg₂ Set.inter hp hq
  | sep p q hp hq =>
      change Matching.FixedPoint.application (matchingModel M) .join
        (fun i => (matchingModel M).denote (fun j : Fin 0 => j.elim0)
          (Fin.cases (compileBase p) (fun _ => compileBase q) i)) = _
      rw [pair_map, hp, hq]
      exact join_application M _ _
  | wand p q hp hq =>
      change (Matching.FixedPoint.application (matchingModel M) .extension
        (fun i => (matchingModel M).denote (fun j : Fin 0 => j.elim0)
          (Fin.cases (compileBase p) (fun _ => .neg (compileBase q)) i)))ᶜ = _
      rw [pair_map, hp]
      change (Matching.FixedPoint.application (matchingModel M) .extension
        (Fin.cases (p.denote M) (fun _ => ((matchingModel M).denote
          (fun j : Fin 0 => j.elim0) (compileBase q))ᶜ)))ᶜ = _
      rw [hq]
      exact extension_negative M _ _

theorem compilePattern_denote (M : Model A) {r} (p : Pattern A r) :
    (compilePattern p).denote (matchingModel M) (fun i : Fin 0 => i.elim0) = p.denote M := by
  induction p with
  | base p => exact OrderHom.ext _ _ (funext fun _ => compileBase_denote M p)
  | var i => rfl
  | conj p q hp hq =>
      apply OrderHom.ext
      funext η
      exact congrArg₂ Set.inter (congrArg (fun F => F η) hp) (congrArg (fun F => F η) hq)
  | disj p q hp hq =>
      apply OrderHom.ext
      funext η
      exact congrArg₂ Set.union (congrArg (fun F => F η) hp) (congrArg (fun F => F η) hq)
  | sep p q hp hq =>
      apply OrderHom.ext
      funext η
      change Matching.FixedPoint.application (matchingModel M) .join
        (fun i => Matching.FixedPoint.Pattern.denote (matchingModel M)
          (Fin.cases (compilePattern p) (fun _ => compilePattern q) i) (fun j : Fin 0 => j.elim0) η) = _
      rw [pair_map (fun t : MatchingPattern A _ => t.denote (matchingModel M) (fun j : Fin 0 => j.elim0) η), hp, hq]
      exact join_application M _ _
  | wand p q hq =>
      show (compilePattern (.wand p q)).denote (matchingModel M)
        (fun i : Fin 0 => i.elim0) = Pattern.denote M (.wand p q)
      apply OrderHom.ext
      funext η
      change Matching.FixedPoint.dualApplication (matchingModel M) .extension
        (fun i => Matching.FixedPoint.Pattern.denote (matchingModel M)
          (Fin.cases (.base (.neg (compileBase p))) (fun _ => compilePattern q) i) (fun j : Fin 0 => j.elim0) η) = _
      rw [pair_map (fun t : MatchingPattern A _ => t.denote (matchingModel M) (fun j : Fin 0 => j.elim0) η), hq]
      change Matching.FixedPoint.dualApplication (matchingModel M) .extension
        (Fin.cases (((matchingModel M).denote (fun j : Fin 0 => j.elim0) (compileBase p))ᶜ)
          (fun _ => q.denote M η)) = _
      rw [compileBase_denote]
      exact extension_dual M _ _
  | mu p hp =>
      apply OrderHom.ext
      funext η
      apply congrArg OrderHom.lfp
      apply OrderHom.ext
      funext X
      exact congrArg (fun F => F (Fin.cases X η)) hp

theorem encode_satisfaction (M : Model A) (p : Sentence A) :
    (encode p).Satisfies (matchingModel M) ↔ p.Satisfies M := by
  classical
  have he : (fun i : Fin 0 => ((fun j : Fin 0 => (j.elim0 : Set M.resource.carrier)) i)ᶜ) =
      (fun i : Fin 0 => i.elim0) := funext fun i => i.elim0
  have hd : (compilePattern p.pre).dual.denote (matchingModel M) (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => ((fun j : Fin 0 => (j.elim0 : Set M.resource.carrier)) i)ᶜ) =
      ((compilePattern p.pre).denote (matchingModel M) (fun i => i.elim0) (fun i => i.elim0))ᶜ := (compilePattern p.pre).denote_dual (matchingModel M) (fun i : Fin 0 => i.elim0)
    (fun i : Fin 0 => i.elim0)
  have hpre : (compilePattern p.pre).denote (matchingModel M) (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) = p.pre.denote M (fun i => i.elim0) :=
    congrArg (fun F => F (fun i => i.elim0)) (compilePattern_denote M p.pre)
  have hpost : (compilePattern p.post).denote (matchingModel M) (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) = p.post.denote M (fun i => i.elim0) :=
    congrArg (fun F => F (fun i => i.elim0)) (compilePattern_denote M p.post)
  have hd' : (compilePattern p.pre).dual.denote (matchingModel M) (fun i : Fin 0 => i.elim0)
      (fun i : Fin 0 => i.elim0) = (p.pre.denote M (fun i => i.elim0))ᶜ := by
    calc
      _ = (compilePattern p.pre).dual.denote (matchingModel M) (fun i : Fin 0 => i.elim0)
          (fun i : Fin 0 => ((fun j : Fin 0 => (j.elim0 : Set M.resource.carrier)) i)ᶜ) :=
        congrArg (fun η => (compilePattern p.pre).dual.denote (matchingModel M)
          (fun i : Fin 0 => i.elim0) η) he.symm
      _ = ((compilePattern p.pre).denote (matchingModel M)
          (fun i => i.elim0) (fun i => i.elim0))ᶜ := hd
      _ = _ := congrArg Set.compl hpre
  constructor
  · show (encode p).Satisfies (matchingModel M) → p.Satisfies M
    intro h x hx
    have ht : x ∈ (encode p).pattern.denote (matchingModel M) (fun i => i.elim0) (fun i => i.elim0) :=
      h (fun i => i.elim0) (fun i => i.elim0) x
    change x ∈ (compilePattern p.pre).dual.denote (matchingModel M) _ _ ∪
      (compilePattern p.post).denote (matchingModel M) _ _ at ht
    have ht' : x ∈ (p.pre.denote M (fun i => i.elim0))ᶜ ∪ p.post.denote M (fun i => i.elim0) := by
      rw [← hd', ← hpost]
      exact ht
    exact ht'.elim (fun hn => False.elim (hn hx)) id
  · show p.Satisfies M → (encode p).Satisfies (matchingModel M)
    intro h v η x
    have hv : v = fun i => i.elim0 := funext fun i => i.elim0
    have hη : η = fun i => i.elim0 := funext fun i => i.elim0
    rw [hv, hη]
    change x ∈ (compilePattern p.pre).dual.denote (matchingModel M) _ _ ∪
      (compilePattern p.post).denote (matchingModel M) _ _
    rw [hd', hpost]
    exact (Classical.em (x ∈ p.pre.denote M (fun i => i.elim0))).elim
      (fun hp => Or.inr (h hp)) Or.inl


end Silmaril.Logic.Separation
