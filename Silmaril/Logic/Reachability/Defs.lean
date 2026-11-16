module

public import Silmaril.Logic.Matching.FixedPoint
public import Silmaril.Logic.CTL

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Reachability
open CategoryTheory Silmaril.Logic.Institution
variable {S : Type} (cfg : S)

/-- An actual matching signature with a distinguished predecessor-oriented step symbol. -/
structure Signature where
  algebra : Algebraic.ManySorted.Signature S
  step : algebra.operations 1 (fun _ => cfg) cfg

structure Signature.Hom (A B : Signature cfg) where
  algebra : A.algebra ⟶ B.algebra
  step : algebra.operations A.step = B.step

@[ext] theorem Signature.Hom.ext {A B : Signature cfg} (f g : Signature.Hom cfg A B)
    (h : f.algebra = g.algebra) : f = g := by cases f; cases g; cases h; rfl

instance : Category (Signature cfg) where
  Hom := Signature.Hom cfg
  id A := ⟨𝟙 A.algebra, rfl⟩
  comp f g := ⟨f.algebra ≫ g.algebra, by change g.algebra.operations (f.algebra.operations _) = _; rw [f.step, g.step]⟩
  id_comp f := Signature.Hom.ext cfg _ _ (Category.id_comp _)
  comp_id f := Signature.Hom.ext cfg _ _ (Category.comp_id _)
  assoc f g h := Signature.Hom.ext cfg _ _ (Category.assoc _ _ _)

def signatures : Signature cfg ⥤ Algebraic.ManySorted.Signature S where
  obj A := A.algebra
  map f := f.algebra

abbrev Model (A : Signature cfg) := Matching.FirstOrder.Model A.algebra

def step {A : Signature cfg} (M : Model cfg A) (w v : M.carrier cfg) : Prop :=
  w ∈ M.operation A.step (fun _ => v)

/-- The two partial modes are the unconditional fragment of 2013/2014 reachability.
Finite reachability is deliberately separate from one-path partial correctness. -/
inductive Mode | finite | onePath | allPath

/-- All paths here are finite complete paths, exactly as in 2014 Definition 4. -/
def AllPartial {W : Type} (R : W → W → Prop) (Q : W → Prop) (w : W) : Prop :=
  ∀ (n : Nat) (path : Nat → W), path 0 = w →
    (∀ i, i < n → R (path i) (path (i+1))) → (∀ v, ¬ R (path n) v) →
      ∃ i, i ≤ n ∧ Q (path i)

def Reaches {W : Type} (R : W → W → Prop) (Q : W → Prop) (w : W) : Prop :=
  CTL.Until R (fun _ => True) Q w

def Diverges {W : Type} (R : W → W → Prop) (w : W) : Prop :=
  CTL.Globally R (fun _ => True) w

def Mode.Holds {W : Type} : Mode → (W → W → Prop) → (W → Prop) → W → Prop
  | .finite, R, Q, w => Reaches R Q w
  | .onePath, R, Q, w => Reaches R Q w ∨ Diverges R w
  | .allPath, R, Q, w => AllPartial R Q w

structure Sentence (A : Signature cfg) where
  variableCount : Nat
  context : Fin variableCount → S
  mode : Mode
  pre : Matching.FirstOrder.Pattern A.algebra context cfg
  post : Matching.FirstOrder.Pattern A.algebra context cfg

def Sentence.map {A B : Signature cfg} (f : A ⟶ B) (p : Sentence cfg A) : Sentence cfg B :=
  ⟨p.variableCount, p.context, p.mode, p.pre.map f.algebra, p.post.map f.algebra⟩

/-- Source validity quantifies every configuration under the same captured valuation. -/
def Sentence.Satisfies {A : Signature cfg} (M : Model cfg A) (p : Sentence cfg A) : Prop :=
  ∀ (v : ((i : Fin p.variableCount) → M.carrier (p.context i))) (w : M.carrier cfg),
    w ∈ M.denote v p.pre → p.mode.Holds (step cfg M) (fun x => x ∈ M.denote v p.post) w

abbrev Pattern {A : Signature cfg} {k : Nat} (Γ : Fin k → S) :=
  Matching.FixedPoint.Pattern A.algebra (r := 0) (fun _ => cfg) Γ cfg

/-- The fixed object context is captured by μ; no set-variable substitution is needed. -/
def reachPattern {A : Signature cfg} {k : Nat} {Γ : Fin k → S}
    (q : Matching.FirstOrder.Pattern A.algebra Γ cfg) : Pattern cfg (A := A) Γ :=
  .mu (P' := fun _ => cfg) (.disj (.base q) (.app A.step (fun _ => .setvar 0)))

def divergePattern {A : Signature cfg} {k : Nat} {Γ : Fin k → S} : Pattern cfg (A := A) Γ :=
  .nu (P' := fun _ => cfg) (.app A.step (fun _ => .setvar 0))

/-- A finite avoiding prefix reaches an actual terminal state. -/
def badPattern {A : Signature cfg} {k : Nat} {Γ : Fin k → S}
    (q : Matching.FirstOrder.Pattern A.algebra Γ cfg) : Pattern cfg (A := A) Γ :=
  .mu (P' := fun _ => cfg) (.disj
    (.conj (.dualApp A.step (fun _ => .base Matching.FirstOrder.Pattern.bottom)) (.base (.neg q)))
    (.conj (.base (.neg q)) (.app A.step (fun _ => .setvar 0))))

def outcomePattern {A : Signature cfg} (p : Sentence cfg A) : Pattern cfg (A := A) p.context :=
  match p.mode with
  | .finite => reachPattern cfg p.post
  | .onePath => .disj (reachPattern cfg p.post) (divergePattern cfg)
  | .allPath => (badPattern cfg p.post).dual

def encode {A : Signature cfg} (p : Sentence cfg A) : Matching.FixedPoint.Sentence A.algebra :=
  ⟨0, p.variableCount, (fun _ => cfg), p.context, cfg,
    .disj (.base (.neg p.pre)) (outcomePattern cfg p)⟩

end Silmaril.Logic.Reachability
