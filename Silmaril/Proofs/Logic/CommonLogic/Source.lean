module

public import Silmaril.Logic.CommonLogic.Source.Defs

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source
open CategoryTheory Silmaril.Logic.Institution

theorem assignment_cons {α : Type} (names : List String) (ρ : Fin names.length → α)
    (name : String) (x : α) :
    assignment (name::names) (Fin.cases x ρ) = bind (assignment names ρ) name x := by
  funext key
  simp only [assignment, index?, bind]
  split <;> simp_all [Option.map_map, Function.comp_def]

theorem Expr.elaborate_eval {S : Core.Signature} (names : Names S) (M : Core.Model S)
    {a : Core.Kind} (raw : Expr a) (ι κ : List String)
    (ρ : Fin ι.length → M.Discourse) (σ : Fin κ.length → List M.Discourse) :
    (raw.elaborate names ι κ).map (fun t => t.eval M ρ σ) =
      raw.eval names M (assignment ι ρ) (assignment κ σ) := by
  induction raw with
  | individual name =>
      cases hi : index? name ι <;> cases hn : find? name names.discourse <;>
        simp [elaborate, eval, assignment, Core.Expr.eval, hi, hn]
  | reference name =>
      cases hi : index? name ι <;> cases hn : find? name names.discourse <;>
        cases hd : find? name names.nondiscourse <;>
        simp [elaborate, eval, assignment, Core.Expr.eval, hi, hn, hd]
  | sequence name =>
      cases hi : index? name κ <;> cases hn : find? name names.marker <;>
        simp [elaborate, eval, assignment, Core.Expr.eval, hi, hn]
  | lift t ih =>
      simp only [elaborate, eval]
      rw [← ih]
      cases t.elaborate names ι κ <;> rfl
  | app h args ih ia =>
      simp only [elaborate, eval]
      rw [← ih, ← ia]
      cases h.elaborate names ι κ <;> cases args.elaborate names ι κ <;> rfl
  | nil => rfl
  | cons t ts it its =>
      simp only [elaborate, eval]
      rw [← it, ← its]
      cases t.elaborate names ι κ <;> cases ts.elaborate names ι κ <;> rfl
  | append xs ys ix iy =>
      simp only [elaborate, eval]
      rw [← ix, ← iy]
      cases xs.elaborate names ι κ <;> cases ys.elaborate names ι κ <;> rfl

theorem Expr.eval_of_elaborated {S : Core.Signature} (names : Names S) (M : Core.Model S)
    {a : Core.Kind} {raw : Expr a} {ι κ : List String} {typed : Core.Expr S ι.length κ.length a}
    (decoded : raw.elaborate names ι κ = some typed)
    (ρ : Fin ι.length → M.Discourse) (σ : Fin κ.length → List M.Discourse) :
    raw.eval names M (assignment ι ρ) (assignment κ σ) = some (typed.eval M ρ σ) := by
  rw [← raw.elaborate_eval names M ι κ ρ σ, decoded]
  rfl

theorem Formula.holds_of_elaborated {S : Core.Signature} (names : Names S) (M : Core.Model S)
    (raw : Formula) : ∀ (ι κ : List String) (typed : Core.Formula S ι.length κ.length),
    raw.elaborate names ι κ = some typed →
    ∀ (ρ : Fin ι.length → M.Discourse) (σ : Fin κ.length → List M.Discourse),
      raw.Holds names M (assignment ι ρ) (assignment κ σ) ↔ typed.Holds M ρ σ := by
  induction raw with
  | equal t u =>
      intro ι κ typed h ρ σ
      cases ht : t.elaborate names ι κ <;> cases hu : u.elaborate names ι κ <;>
        simp [elaborate, ht, hu] at h
      subst typed
      simp only [Holds, Core.Formula.Holds, t.eval_of_elaborated names M ht ρ σ,
        u.eval_of_elaborated names M hu ρ σ, Option.some.injEq]
      constructor
      · rintro ⟨x,y,hx,hy,h⟩
        simpa only [← hx, ← hy] using h
      · intro h
        exact ⟨_,_,rfl,rfl,h⟩
  | pred t ts =>
      intro ι κ typed h ρ σ
      cases ht : t.elaborate names ι κ <;> cases hs : ts.elaborate names ι κ <;>
        simp [elaborate, ht, hs] at h
      subst typed
      simp only [Holds, Core.Formula.Holds, t.eval_of_elaborated names M ht ρ σ,
        ts.eval_of_elaborated names M hs ρ σ, Option.some.injEq]
      constructor
      · rintro ⟨x,y,hx,hy,h⟩
        simpa only [← hx, ← hy] using h
      · intro h
        exact ⟨_,_,rfl,rfl,h⟩
  | tt | ff =>
      intro ι κ typed h ρ σ
      simp only [elaborate, Option.some.injEq] at h
      subst typed
      rfl
  | neg p ih =>
      intro ι κ typed h ρ σ
      cases hp : p.elaborate names ι κ <;> simp [elaborate, hp] at h
      subst typed
      exact not_congr (ih ι κ _ hp ρ σ)
  | conj p q ip iq =>
      intro ι κ typed h ρ σ
      cases hp : p.elaborate names ι κ <;> cases hq : q.elaborate names ι κ <;>
        simp [elaborate, hp, hq] at h
      subst typed
      exact and_congr (ip ι κ _ hp ρ σ) (iq ι κ _ hq ρ σ)
  | disj p q ip iq =>
      intro ι κ typed h ρ σ
      cases hp : p.elaborate names ι κ <;> cases hq : q.elaborate names ι κ <;>
        simp [elaborate, hp, hq] at h
      subst typed
      exact or_congr (ip ι κ _ hp ρ σ) (iq ι κ _ hq ρ σ)
  | impl p q ip iq =>
      intro ι κ typed h ρ σ
      cases hp : p.elaborate names ι κ <;> cases hq : q.elaborate names ι κ <;>
        simp [elaborate, hp, hq] at h
      subst typed
      exact imp_congr (ip ι κ _ hp ρ σ) (iq ι κ _ hq ρ σ)
  | iff p q ip iq =>
      intro ι κ typed h ρ σ
      cases hp : p.elaborate names ι κ <;> cases hq : q.elaborate names ι κ <;>
        simp [elaborate, hp, hq] at h
      subst typed
      exact iff_congr (ip ι κ _ hp ρ σ) (iq ι κ _ hq ρ σ)
  | all name p ih =>
      intro ι κ typed h ρ σ
      cases hp : p.elaborate names (name::ι) κ <;> simp [elaborate, hp] at h
      subst typed
      apply forall_congr'
      intro x
      simpa only [assignment_cons] using ih (name::ι) κ _ hp (Fin.cases x ρ) σ
  | ex name p ih =>
      intro ι κ typed h ρ σ
      cases hp : p.elaborate names (name::ι) κ <;> simp [elaborate, hp] at h
      subst typed
      apply exists_congr
      intro x
      simpa only [assignment_cons] using ih (name::ι) κ _ hp (Fin.cases x ρ) σ
  | allSeq name p ih =>
      intro ι κ typed h ρ σ
      cases hp : p.elaborate names ι (name::κ) <;> simp [elaborate, hp] at h
      subst typed
      apply forall_congr'
      intro x
      simpa only [assignment_cons] using ih ι (name::κ) _ hp ρ (Fin.cases x σ)
  | exSeq name p ih =>
      intro ι κ typed h ρ σ
      cases hp : p.elaborate names ι (name::κ) <;> simp [elaborate, hp] at h
      subst typed
      apply exists_congr
      intro x
      simpa only [assignment_cons] using ih ι (name::κ) _ hp ρ (Fin.cases x σ)

theorem find?_map {α β : Type} (f : α → β) (name : String) (entries : List (String × α)) :
    find? name (entries.map (fun p => (p.1, f p.2))) = (find? name entries).map f := by
  induction entries with
  | nil => rfl
  | cons p rest ih =>
      simp only [List.map_cons, find?]
      split <;> simp_all

theorem Names.valid_map {S T : Core.Signature} (names : Names S) (f : S ⟶ T)
    (valid : names.Valid) : (names.map f).Valid := by
  simpa only [Names.Valid, Names.map, List.map_map, Function.comp_def] using valid

theorem Expr.elaborate_map {S T : Core.Signature} (names : Names S) (f : S ⟶ T)
    {a : Core.Kind} (raw : Expr a) (ι κ : List String) :
    raw.elaborate (names.map f) ι κ = (raw.elaborate names ι κ).map (Core.Expr.map f) := by
  induction raw with
  | individual key =>
      cases hi : index? key ι <;> simp only [elaborate, hi, Names.map, find?_map]
      · cases find? key names.discourse <;> rfl
      · rfl
  | reference key =>
      cases hi : index? key ι <;> simp only [elaborate, hi, Names.map, find?_map]
      · cases find? key names.discourse <;> cases find? key names.nondiscourse <;> rfl
      · rfl
  | sequence key =>
      cases hi : index? key κ <;> simp only [elaborate, hi, Names.map, find?_map]
      · cases find? key names.marker <;> rfl
      · rfl
  | lift t ih =>
      simp only [elaborate, ih]
      cases t.elaborate names ι κ <;> rfl
  | app h args ih ia =>
      simp only [elaborate, ih, ia]
      cases h.elaborate names ι κ <;> cases args.elaborate names ι κ <;> rfl
  | nil => rfl
  | cons t ts it its =>
      simp only [elaborate, it, its]
      cases t.elaborate names ι κ <;> cases ts.elaborate names ι κ <;> rfl
  | append xs ys ix iy =>
      simp only [elaborate, ix, iy]
      cases xs.elaborate names ι κ <;> cases ys.elaborate names ι κ <;> rfl

theorem Formula.elaborate_map {S T : Core.Signature} (names : Names S) (f : S ⟶ T)
    (raw : Formula) : ∀ ι κ, raw.elaborate (names.map f) ι κ =
      (raw.elaborate names ι κ).map (Core.Formula.map f) := by
  induction raw with
  | equal t u | pred t u =>
      intro ι κ
      simp only [elaborate, Expr.elaborate_map]
      cases t.elaborate names ι κ <;> cases u.elaborate names ι κ <;> rfl
  | tt | ff => intros; rfl
  | neg p ih =>
      intro ι κ
      simp only [elaborate, ih]
      cases p.elaborate names ι κ <;> rfl
  | conj p q ip iq | disj p q ip iq | impl p q ip iq | iff p q ip iq =>
      intro ι κ
      simp only [elaborate, ip, iq]
      cases p.elaborate names ι κ <;> cases q.elaborate names ι κ <;> rfl
  | all name p ih | ex name p ih =>
      intro ι κ
      simp only [elaborate, ih]
      cases p.elaborate names (name::ι) κ <;> rfl
  | allSeq name p ih | exSeq name p ih =>
      intro ι κ
      simp only [elaborate, ih]
      cases p.elaborate names ι (name::κ) <;> rfl

def Sentence.map {S T : Core.Signature} {names : Names S} (f : S ⟶ T)
    (p : Sentence names) : Sentence (names.map f) where
  declarations_valid := names.valid_map f p.declarations_valid
  raw := p.raw
  typed := p.typed.map f
  decoded := by rw [p.raw.elaborate_map, p.decoded]; rfl

/-- The source and typed rooms share the actual Core model category. -/
def toCore {S : Core.Signature} (names : Names S) : room names ⟶ Core.room S where
  sen p := p.typed
  mod := 𝟭 _
  sat M p := by
    exact
      (p.raw.holds_of_elaborated names M [] [] p.typed p.decoded Fin.elim0 Fin.elim0).symm

/-- Actual arbitrary Core symbol maps, retaining source spellings and all model arrows. -/
def corridor {S T : Core.Signature} (names : Names S) (f : S ⟶ T) :
    room names ⟶ room (names.map f) where
  sen := Sentence.map f
  mod := Core.Model.reduct f
  sat M p :=
    ((toCore (names.map f)).sat M (p.map f)).symm.trans
      ((Core.Formula.holds_map f M Fin.elim0 Fin.elim0 p.typed).trans
        ((toCore names).sat ((Core.Model.reduct f).obj M) p))

end Silmaril.Logic.CommonLogic.Source
