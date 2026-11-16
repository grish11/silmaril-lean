module

public import Silmaril.Logic.Matching.FixedPoint.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint
open Algebraic.ManySorted (Signature)
variable {S : Type}

/-- Intrinsically sorted variable renamings. -/
abbrev Ren {k l : Nat} (Γ : Fin k → S) (Δ : Fin l → S) := ∀ i, {j : Fin l // Δ j = Γ i}

def Ren.lift {k l : Nat} {Γ : Fin k → S} {Δ : Fin l → S} (ρ : Ren Γ Δ) (s : S) :
    Ren (Fin.cases s Γ) (Fin.cases s Δ) :=
  Fin.cases ⟨0, rfl⟩ (fun i => ⟨(ρ i).val.succ, (ρ i).property⟩)

def Ren.liftHead {r l : Nat} {P' : Fin (r+1) → S} {Q : Fin l → S}
    (ρ : Ren (P' ∘ Fin.succ) Q) : Ren P' (Fin.cases (P' 0) Q) :=
  Fin.cases ⟨0, rfl⟩ (fun i => ⟨(ρ i).val.succ, (ρ i).property⟩)

def Ren.shift {k : Nat} (Γ : Fin k → S) (s : S) : Ren Γ (Fin.cases s Γ) :=
  fun i => ⟨i.succ, rfl⟩

def Ren.pull (D : S → Type) {k l : Nat} {Γ : Fin k → S} {Δ : Fin l → S}
    (v : ∀ j, D (Δ j)) (ρ : Ren Γ Δ) : ∀ i, D (Γ i) :=
  fun i => (ρ i).property ▸ v (ρ i).val

theorem Ren.pull_lift (D : S → Type) {k l : Nat} {Γ : Fin k → S} {Δ : Fin l → S}
    (v : ∀ j, D (Δ j)) (ρ : Ren Γ Δ) (s : S) (x : D s) :
    Ren.pull D (Fin.cases x v) (ρ.lift s) = Fin.cases x (Ren.pull D v ρ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

def renameFirstOrder {A : Signature S} {k : Nat} {Γ : Fin k → S} {s : S}
    (p : FirstOrder.Pattern A Γ s) :
    {l : Nat} → {Δ : Fin l → S} → Ren Γ Δ → FirstOrder.Pattern A Δ s := by
  induction p with
  | var i => intro l Δ ρ; exact (ρ i).property ▸ FirstOrder.Pattern.var (ρ i).val
  | app op args ih => intro l Δ ρ; exact .app op (fun i => ih i ρ)
  | neg p hp => intro l Δ ρ; exact .neg (hp ρ)
  | conj p q hp hq => intro l Δ ρ; exact .conj (hp ρ) (hq ρ)
  | ex bound p hp => intro l Δ ρ; exact .ex bound (hp (ρ.lift bound))

theorem denote_var_cast {A : Signature S} (M : Model A) {l : Nat} {Δ : Fin l → S}
    (v : ObjEnv A M Δ) {t : S} (j : Fin l) (h : Δ j = t) :
    M.denote v (h ▸ FirstOrder.Pattern.var j) = {h ▸ v j} := by
  cases h
  rfl

theorem renameFirstOrder_denote {A : Signature S} (M : Model A) {k : Nat}
    {Γ : Fin k → S} {s : S} (p : FirstOrder.Pattern A Γ s) :
    ∀ {l : Nat} {Δ : Fin l → S} (ρ : Ren Γ Δ) (v : ObjEnv A M Δ),
      M.denote v (renameFirstOrder p ρ) = M.denote (Ren.pull M.carrier v ρ) p := by
  induction p with
  | var i =>
      intro l Δ ρ v
      exact denote_var_cast M v (ρ i).val (ρ i).property
  | app op args ih =>
      intro l Δ ρ v
      change application M op (fun i => M.denote v (renameFirstOrder (args i) ρ)) = _
      simp only [ih]
      rfl
  | neg p hp => intro l Δ ρ v; exact congrArg (fun X => Xᶜ) (hp ρ v)
  | conj p q hp hq => intro l Δ ρ v; exact congrArg₂ Set.inter (hp ρ v) (hq ρ v)
  | ex bound p hp =>
      intro l Δ ρ v
      change {x | ∃ a : M.carrier bound, x ∈ M.denote (Fin.cases a v) (renameFirstOrder p (ρ.lift bound))} = _
      simp only [hp, Ren.pull_lift]
      rfl

def Pattern.renameObjects {A : Signature S} {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    {l : Nat} → {Δ : Fin l → S} → Ren Γ Δ → Pattern A P Δ s := by
  induction p with
  | base p => intro l Δ ρ; exact .base (renameFirstOrder p ρ)
  | setvar i => intro l Δ ρ; exact .setvar i
  | app op args ih => intro l Δ ρ; exact .app op (fun i => ih i ρ)
  | dualApp op args ih => intro l Δ ρ; exact .dualApp op (fun i => ih i ρ)
  | conj p q hp hq => intro l Δ ρ; exact .conj (hp ρ) (hq ρ)
  | disj p q hp hq => intro l Δ ρ; exact .disj (hp ρ) (hq ρ)
  | ex bound p hp => intro l Δ ρ; exact .ex bound (hp (ρ.lift bound))
  | all bound p hp => intro l Δ ρ; exact .all bound (hp (ρ.lift bound))
  | mu p hp => intro l Δ ρ; exact .mu (hp ρ)
  | nu p hp => intro l Δ ρ; exact .nu (hp ρ)

def Pattern.renameSets {A : Signature S} {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    {l : Nat} → {Q : Fin l → S} → Ren P Q → Pattern A Q Γ s := by
  induction p with
  | base p => intro l Q ρ; exact .base p
  | setvar i => intro l Q ρ; exact (ρ i).property ▸ Pattern.setvar (ρ i).val
  | app op args ih => intro l Q ρ; exact .app op (fun i => ih i ρ)
  | dualApp op args ih => intro l Q ρ; exact .dualApp op (fun i => ih i ρ)
  | conj p q hp hq => intro l Q ρ; exact .conj (hp ρ) (hq ρ)
  | disj p q hp hq => intro l Q ρ; exact .disj (hp ρ) (hq ρ)
  | ex bound p hp => intro l Q ρ; exact .ex bound (hp ρ)
  | all bound p hp => intro l Q ρ; exact .all bound (hp ρ)
  | @mu r k P' Γ p hp =>
      intro l Q ρ
      exact Pattern.mu (P' := Fin.cases (P' 0) Q) (hp (Ren.liftHead ρ))
  | @nu r k P' Γ p hp =>
      intro l Q ρ
      exact Pattern.nu (P' := Fin.cases (P' 0) Q) (hp (Ren.liftHead ρ))

theorem Ren.pull_liftHead (D : S → Type) {r l : Nat} {P' : Fin (r+1) → S}
    {Q : Fin l → S} (v : ∀ j, D (Q j)) (ρ : Ren (P' ∘ Fin.succ) Q) (x : D (P' 0)) :
    Ren.pull D (Fin.cases x v) (Ren.liftHead ρ) = Fin.cases x (Ren.pull D v ρ) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem Pattern.denote_renameObjects {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l : Nat} {Δ : Fin l → S} (ρ : Ren Γ Δ) (v : ObjEnv A M Δ),
      (p.renameObjects ρ).denote M v = p.denote M (Ren.pull M.carrier v ρ) := by
  induction p with
  | base p =>
      intro l Δ ρ v
      apply OrderHom.ext
      funext η
      exact renameFirstOrder_denote M p ρ v
  | setvar => intro l Δ ρ v; rfl
  | app op args ih =>
      intro l Δ ρ v
      apply OrderHom.ext
      funext η
      change application M op (fun i => (renameObjects (args i) ρ).denote M v η) = _
      simp only [ih]
      rfl
  | dualApp op args ih =>
      intro l Δ ρ v
      apply OrderHom.ext
      funext η
      change dualApplication M op (fun i => (renameObjects (args i) ρ).denote M v η) = _
      simp only [ih]
      rfl
  | conj p q hp hq =>
      intro l Δ ρ v
      apply OrderHom.ext
      funext η
      change (p.renameObjects ρ).denote M v η ∩ (q.renameObjects ρ).denote M v η = _
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      intro l Δ ρ v
      apply OrderHom.ext
      funext η
      change (p.renameObjects ρ).denote M v η ∪ (q.renameObjects ρ).denote M v η = _
      rw [hp, hq]
      rfl
  | ex bound p hp =>
      intro l Δ ρ v
      apply OrderHom.ext
      funext η
      change {x | ∃ a : M.carrier bound, x ∈ (p.renameObjects (ρ.lift bound)).denote M (Fin.cases a v) η} = _
      simp only [hp, Ren.pull_lift]
      rfl
  | all bound p hp =>
      intro l Δ ρ v
      apply OrderHom.ext
      funext η
      change {x | ∀ a : M.carrier bound, x ∈ (p.renameObjects (ρ.lift bound)).denote M (Fin.cases a v) η} = _
      simp only [hp, Ren.pull_lift]
      rfl
  | mu p hp =>
      intro l Δ ρ v
      apply OrderHom.ext
      funext η
      change (((p.renameObjects ρ).denote M v).comp (insert _ M η)).lfp = _
      rw [hp]
      rfl
  | nu p hp =>
      intro l Δ ρ v
      apply OrderHom.ext
      funext η
      change (((p.renameObjects ρ).denote M v).comp (insert _ M η)).gfp = _
      rw [hp]
      rfl

theorem denote_setvar_cast {A : Signature S} (M : Model A) {r k : Nat}
    {Q : Fin r → S} {Γ : Fin k → S} (v : ObjEnv A M Γ) (η : SetEnv A M Q)
    {t : S} (j : Fin r) (h : Q j = t) :
    (h ▸ Pattern.setvar (A := A) (Γ := Γ) (P := Q) j).denote M v η = h ▸ η j := by
  cases h
  rfl

theorem Pattern.denote_renameSets {A : Signature S} (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ {l : Nat} {Q : Fin l → S} (ρ : Ren P Q) (v : ObjEnv A M Γ) (η : SetEnv A M Q),
      (p.renameSets ρ).denote M v η = p.denote M v (Ren.pull (fun s => Set (M.carrier s)) η ρ) := by
  induction p with
  | base => intro l Q ρ v η; rfl
  | setvar i => intro l Q ρ v η; exact denote_setvar_cast M v η (ρ i).val (ρ i).property
  | app op args ih =>
      intro l Q ρ v η
      change application M op (fun i => (renameSets (args i) ρ).denote M v η) = _
      simp only [ih]
      rfl
  | dualApp op args ih =>
      intro l Q ρ v η
      change dualApplication M op (fun i => (renameSets (args i) ρ).denote M v η) = _
      simp only [ih]
      rfl
  | conj p q hp hq =>
      intro l Q ρ v η
      exact congrArg₂ Set.inter (hp ρ v η) (hq ρ v η)
  | disj p q hp hq =>
      intro l Q ρ v η
      exact congrArg₂ Set.union (hp ρ v η) (hq ρ v η)
  | ex bound p hp =>
      intro l Q ρ v η
      change {x | ∃ a : M.carrier bound, x ∈ (p.renameSets ρ).denote M (Fin.cases a v) η} = _
      simp only [hp]
      rfl
  | all bound p hp =>
      intro l Q ρ v η
      change {x | ∀ a : M.carrier bound, x ∈ (p.renameSets ρ).denote M (Fin.cases a v) η} = _
      simp only [hp]
      rfl
  | @mu r k P' Γ p hp =>
      show ∀ {l} {Q : Fin l → S} (ρ : Ren (P' ∘ Fin.succ) Q) v η,
        ((Pattern.mu p).renameSets ρ).denote M v η =
          (Pattern.mu p).denote M v (Ren.pull (fun s => Set (M.carrier s)) η ρ)
      intro l Q ρ v η
      apply congrArg OrderHom.lfp
      apply OrderHom.ext
      funext X
      change (p.renameSets (Ren.liftHead ρ)).denote M v (Fin.cases X η) = _
      exact (hp (Ren.liftHead ρ) v (Fin.cases X η)).trans
        (congrArg (fun env => p.denote M v env)
          (Ren.pull_liftHead (fun s => Set (M.carrier s)) η ρ X))
  | @nu r k P' Γ p hp =>
      show ∀ {l} {Q : Fin l → S} (ρ : Ren (P' ∘ Fin.succ) Q) v η,
        ((Pattern.nu p).renameSets ρ).denote M v η =
          (Pattern.nu p).denote M v (Ren.pull (fun s => Set (M.carrier s)) η ρ)
      intro l Q ρ v η
      apply congrArg OrderHom.gfp
      apply OrderHom.ext
      funext X
      change (p.renameSets (Ren.liftHead ρ)).denote M v (Fin.cases X η) = _
      exact (hp (Ren.liftHead ρ) v (Fin.cases X η)).trans
        (congrArg (fun env => p.denote M v env)
          (Ren.pull_liftHead (fun s => Set (M.carrier s)) η ρ X))

/-- Simultaneous, capture-avoiding substitution of positive set patterns.
Object binders shift replacement objects; set binders shift replacement sets. -/
def Pattern.substituteSets {A : Signature S} {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    {l : Nat} → {Q : Fin l → S} → (∀ i, Pattern A Q Γ (P i)) → Pattern A Q Γ s := by
  induction p with
  | base p => intro l Q σ; exact .base p
  | setvar i => intro l Q σ; exact σ i
  | app op args ih => intro l Q σ; exact .app op (fun i => ih i σ)
  | dualApp op args ih => intro l Q σ; exact .dualApp op (fun i => ih i σ)
  | conj p q hp hq => intro l Q σ; exact .conj (hp σ) (hq σ)
  | disj p q hp hq => intro l Q σ; exact .disj (hp σ) (hq σ)
  | ex bound p hp => intro l Q σ; exact .ex bound (hp (fun i => (σ i).renameObjects (Ren.shift _ bound)))
  | all bound p hp => intro l Q σ; exact .all bound (hp (fun i => (σ i).renameObjects (Ren.shift _ bound)))
  | @mu r k P' Γ p hp =>
      intro l Q σ
      exact Pattern.mu (P' := Fin.cases (P' 0) Q) (hp (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))) :
        ∀ i, Pattern A (Fin.cases (P' 0) Q) Γ (P' i)))
  | @nu r k P' Γ p hp =>
      intro l Q σ
      exact Pattern.nu (P' := Fin.cases (P' 0) Q) (hp (Fin.cases (.setvar 0) (fun i => (σ i).renameSets (Ren.shift Q (P' 0))) :
        ∀ i, Pattern A (Fin.cases (P' 0) Q) Γ (P' i)))

end Silmaril.Logic.Matching.FixedPoint
