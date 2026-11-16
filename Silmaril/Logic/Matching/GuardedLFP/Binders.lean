module

public import Silmaril.Logic.Matching.FixedPoint

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open Algebraic.ManySorted (Signature)

/-- A recursive block of tuple components, followed by the captured context. -/
def blockContext {S : Type} {k : Nat} (Γ : Fin k → S) :
    {n : Nat} → (Fin n → S) → Fin (k+n) → S
  | 0, _ => Γ
  | _+1, w => Fin.cases (w 0) (blockContext Γ (w ∘ Fin.succ))

def prefixIndex {k : Nat} : {n : Nat} → Fin n → Fin (k+n)
  | 0, i => i.elim0
  | _+1, i => Fin.cases 0 (fun j => (prefixIndex j).succ) i

def ambientIndex {k : Nat} : (n : Nat) → Fin k → Fin (k+n)
  | 0, i => i
  | n+1, i => (ambientIndex n i).succ

theorem blockContext_prefix {S : Type} {k n : Nat} (Γ : Fin k → S)
    (w : Fin n → S) (i : Fin n) : blockContext Γ w (prefixIndex i) = w i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih => exact Fin.cases rfl (fun j => ih (w ∘ Fin.succ) j) i

theorem blockContext_ambient {S : Type} {k n : Nat} (Γ : Fin k → S)
    (w : Fin n → S) (i : Fin k) : blockContext Γ w (ambientIndex n i) = Γ i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (w ∘ Fin.succ)

/-- Reindex a source tuple-prefix context into the recursive binder block. -/
def blockIndex {k n : Nat} : Fin (n+k) → Fin (k+n) :=
  Fin.addCases prefixIndex (ambientIndex n)

theorem blockIndex_prefix {k n : Nat} (i : Fin n) :
    blockIndex (Fin.castAdd k i) = prefixIndex (k := k) i := Fin.addCases_left i

theorem blockIndex_ambient {k n : Nat} (i : Fin k) :
    blockIndex (Fin.natAdd n i) = ambientIndex n i := Fin.addCases_right i

def blockRen {S : Type} {k n : Nat} {Γ : Fin k → S} {w : Fin n → S}
    {Δ : Fin (n+k) → S} (ht : Δ ∘ Fin.castAdd k = w)
    (hp : Δ ∘ Fin.natAdd n = Γ) : FixedPoint.Ren Δ (blockContext Γ w) := fun i =>
  ⟨blockIndex i, by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [blockIndex_prefix]
      exact (blockContext_prefix Γ w j).trans (congrFun ht j).symm
    · rw [blockIndex_ambient]
      exact (blockContext_ambient Γ w j).trans (congrFun hp j).symm⟩

def blockEnv {S : Type} (D : S → Type) {k : Nat} {Γ : Fin k → S}
    (v : ∀ i, D (Γ i)) : {n : Nat} → {w : Fin n → S} →
    (∀ i, D (w i)) → ∀ i, D (blockContext Γ w i)
  | 0, _, _ => v
  | _+1, _, x => Fin.cases (x 0) (blockEnv D v (fun i => x i.succ))

theorem blockEnv_prefix {S : Type} (D : S → Type) {k n : Nat}
    {Γ : Fin k → S} {w : Fin n → S} (v : ∀ i, D (Γ i)) (x : ∀ i, D (w i)) (i : Fin n) :
    HEq (blockEnv D v x (prefixIndex i)) (x i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih => exact Fin.cases HEq.rfl (fun j => ih (fun i => x i.succ) j) i

theorem blockEnv_ambient {S : Type} (D : S → Type) {k n : Nat}
    {Γ : Fin k → S} {w : Fin n → S} (v : ∀ i, D (Γ i)) (x : ∀ i, D (w i)) (i : Fin k) :
    HEq (blockEnv D v x (ambientIndex n i)) (v i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun i => x i.succ)

theorem value_cast_heq {S : Type} (D : S → Type) {a b : S} (h : a = b) (x : D a) :
    HEq (h ▸ x : D b) x := by cases h; rfl

theorem pull_heq {S : Type} (D : S → Type) {k l : Nat}
    {Γ : Fin k → S} {Δ : Fin l → S} (ρ : FixedPoint.Ren Γ Δ)
    (v : ∀ i, D (Δ i)) (i : Fin k) : HEq (FixedPoint.Ren.pull D v ρ i) (v (ρ i).val) := by
  exact value_cast_heq D (ρ i).property (v (ρ i).val)

theorem blockPull_prefix {S : Type} (D : S → Type) {k n : Nat}
    {Γ : Fin k → S} {w : Fin n → S} {Δ : Fin (n+k) → S}
    (ht : Δ ∘ Fin.castAdd k = w) (hp : Δ ∘ Fin.natAdd n = Γ)
    (v : ∀ i, D (Γ i)) (x : ∀ i, D (w i)) (i : Fin n) :
    HEq (FixedPoint.Ren.pull D (blockEnv D v x) (blockRen ht hp) (Fin.castAdd k i)) (x i) := by
  have h := pull_heq D (blockRen ht hp) (blockEnv D v x) (Fin.castAdd k i)
  change HEq _ (blockEnv D v x (blockIndex (Fin.castAdd k i))) at h
  rw [blockIndex_prefix] at h
  exact h.trans (blockEnv_prefix D v x i)

theorem blockPull_ambient {S : Type} (D : S → Type) {k n : Nat}
    {Γ : Fin k → S} {w : Fin n → S} {Δ : Fin (n+k) → S}
    (ht : Δ ∘ Fin.castAdd k = w) (hp : Δ ∘ Fin.natAdd n = Γ)
    (v : ∀ i, D (Γ i)) (x : ∀ i, D (w i)) (i : Fin k) :
    HEq (FixedPoint.Ren.pull D (blockEnv D v x) (blockRen ht hp) (Fin.natAdd n i)) (v i) := by
  have h := pull_heq D (blockRen ht hp) (blockEnv D v x) (Fin.natAdd n i)
  change HEq _ (blockEnv D v x (blockIndex (Fin.natAdd n i))) at h
  rw [blockIndex_ambient] at h
  exact h.trans (blockEnv_ambient D v x i)

/-- Existentially bind the tuple prefix while leaving captured objects free. -/
def bindPrefix {S : Type} {A : Signature S} {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s : S} :
    {n : Nat} → {w : Fin n → S} →
    FixedPoint.Pattern A P (blockContext Γ w) s → FixedPoint.Pattern A P Γ s
  | 0, _, body => body
  | _+1, w, body => bindPrefix (.ex (w 0) body)

theorem bindPrefix_denote {S : Type} {A : Signature S} (M : FixedPoint.Model A)
    {r k n : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S} {w : Fin n → S}
    (body : FixedPoint.Pattern A P (blockContext Γ w) s)
    (v : FixedPoint.ObjEnv A M Γ) (η : FixedPoint.SetEnv A M P) (y : M.carrier s) :
    y ∈ (bindPrefix body).denote M v η ↔
      ∃ x : ∀ i, M.carrier (w i), y ∈ body.denote M (blockEnv M.carrier v x) η := by
  induction n with
  | zero =>
      constructor
      · intro h
        exact ⟨fun i => i.elim0, h⟩
      · rintro ⟨x, h⟩
        exact h
  | succ n ih =>
      change y ∈ (bindPrefix (.ex (w 0) body)).denote M v η ↔ _
      rw [ih]
      constructor
      · rintro ⟨tail, head, h⟩
        refine ⟨Fin.cases head tail, ?_⟩
        change y ∈ body.denote M (Fin.cases head (blockEnv M.carrier v tail)) η at h
        exact h
      · rintro ⟨x, h⟩
        refine ⟨fun i => x i.succ, x 0, ?_⟩
        exact h
end Silmaril.Logic.Matching.GuardedLFP
