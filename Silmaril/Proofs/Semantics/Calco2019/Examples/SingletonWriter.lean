module

public import Silmaril.Semantics.Calco2019.Examples.SingletonWriter.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.SingletonWriter.Proofs

variable {A X Y : Type u}

@[simp] theorem observe_result (word : List A) (x : X) :
    observe (result word x) = .inl (word, x) := by
  change (Equiv.optionEquivSumPUnit _) (Option.map (fun p : X × FreeMonoid A => (p.2.toList, p.1))
    (@Part.toOption _ (Part.some (x, FreeMonoid.ofList word)) (Classical.propDecidable _))) = _
  rw [Part.some_toOption]
  rfl

@[simp] theorem observe_divergence : observe (divergence : Model A X) = .inr PUnit.unit := by
  change (Equiv.optionEquivSumPUnit _) (Option.map (fun p : X × FreeMonoid A => (p.2.toList, p.1))
    (@Part.toOption _ Part.none (Classical.propDecidable _))) = _
  have h : @Part.toOption (X × FreeMonoid A) Part.none (Classical.propDecidable _) = .none :=
    (@Part.toOption_eq_none_iff _ Part.none (Classical.propDecidable _)).2 (by simp)
  rw [h]
  rfl

theorem pure_eq (x : X) : (pure x : Model A X) = result [] x := rfl

private theorem bind_divergence (k : X → Model A Y) : divergence >>= k = divergence := by
  apply WriterT.ext
  simp [Model, divergence, WriterT.run_bind]

private theorem bind_result_divergence (word : List A) (x : X) :
    (result word x >>= fun _ => divergence : Model A Y) = divergence := by
  apply WriterT.ext
  simp [Model, result, divergence, WriterT.run_bind]

private theorem bind_results (word : List A) (x : X) (tail : List A) (y : Y) :
    (result word x >>= fun _ => result tail y) = result (word ++ tail) y := by
  apply WriterT.ext
  simp [Model, result, WriterT.run_bind]

theorem elgot_isElgot (A : Type u) : (elgot A).IsElgot :=
  ofLawfulMonad_isElgot (Model A)

theorem observe_bind (p : Model A X) (k : X → Model A Y) :
    observe (p >>= k) =
      match observe p with
      | .inr _ => .inr PUnit.unit
      | .inl (word, x) =>
        match observe (k x) with
        | .inr _ => .inr PUnit.unit
        | .inl (suffix, y) => .inl (word ++ suffix, y) := by
  cases hp : observe p with
  | inr u =>
    cases u
    have he := observe.injective (hp.trans observe_divergence.symm)
    rw [he, bind_divergence, observe_divergence]
  | inl pair =>
    obtain ⟨word, x⟩ := pair
    have he := observe.injective (hp.trans (observe_result word x).symm)
    rw [he]
    have hbind : (result word x >>= k) = result word x >>= fun _ => k x := by
      apply WriterT.ext
      simp [Model, result, WriterT.run_bind]
    rw [hbind]
    cases hk : observe (k x) with
    | inr u =>
      cases u
      have he := observe.injective (hk.trans observe_divergence.symm)
      rw [he, bind_result_divergence, observe_divergence]
      simp only [hk]
    | inl pair =>
      obtain ⟨suffix, y⟩ := pair
      have he := observe.injective (hk.trans (observe_result suffix y).symm)
      rw [he, bind_results, observe_result]
      simp only [hk]

end Silmaril.Calco2019.Examples.SingletonWriter.Proofs
