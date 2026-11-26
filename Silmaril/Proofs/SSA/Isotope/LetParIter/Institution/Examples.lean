module

import Silmaril.SSA.Isotope.LetParIter.Institution.Restrictions.Thms
import Silmaril.Semantics.Elgot.Thms

/-! A native loop runs in parallel with a partial instruction. The same
translated equation is true when the instruction returns and false when it
is undefined. A false seed exercises an actual feedback step. -/

open CategoryTheory Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetParIter.Institution
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics

namespace LetParIterInstitution

abbrev Sorts := Ty Unit
abbrev Bit : Sorts := .base ()
abbrev One : Sorts := unit
abbrev Val := Ty.denote (fun _ : Unit => Bool)

def coerce : {A B : Sorts} → Ty.Subty A B → Val A → Val B
  | _, _, .refl _, x => x
  | _, _, .trans f g, x => coerce g (coerce f x)
  | _, _, .product f g, (x, y) => (coerce f x, coerce g y)
  | _, _, .coprod f g, x => Sum.map (coerce f) (coerce g) x
  | _, _, .empty _, x => x.elim
  | _, _, .unit _, _ => PUnit.unit

local instance : TypeModel Sorts where
  interp := Val
  productEquiv _ _ := Equiv.refl _
  coprodEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun _ => rfl, fun _ => rfl⟩
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => x.elim, fun x => x.elim⟩
  coe := coerce

local instance : Bot Bool := ⟨false⟩

inductive Op where
  | step
  | probe

def src : Op → Sorts
  | .step => Bit
  | .probe => One

def trg : Op → Sorts
  | .step => coprod One Bit
  | .probe => One

def eff : Op → Bool
  | .step => false
  | .probe => true

def signature {Φ : Type} (label : Φ → Op) : InstrSig Sorts Bool where
  Instr := Φ
  hasTy := ⟨src ∘ label, trg ∘ label⟩
  hasEff := ⟨eff ∘ label⟩

def source := signature (id : Op → Op)
def target := signature (fun f : Option Op => f.getD .probe)

def addOpcode : source ⟶ target where
  instr := some
  source _ := rfl
  target _ := rfl
  effect _ := rfl

theorem added_opcode (f : source.Instr) : addOpcode.instr f ≠ (none : target.Instr) := by
  exact Option.some_ne_none f

def equation : Sentence source Unit where
  Γ := .nil
  n := 1
  β := .snoc .nil Bit
  A := product One One
  lhs := ⟨.par (.iter rfl (.bv 0) (.op .step (.bv 0))) (.op .probe .unit),
    .par (.iter .bv (.op .bv)) (.op .unit)⟩
  rhs := ⟨.pair .unit .unit, .pair .unit .unit⟩

/-- The canonical independent product of two partial values. -/
def pair {A B : Type} (x : Part A) (y : Part B) : Part (A × B) :=
  x.bind fun a => y.map (Prod.mk a)

@[simp] theorem mem_pair {A B : Type} {x : Part A} {y : Part B} {p : A × B} :
    p ∈ pair x y ↔ p.1 ∈ x ∧ p.2 ∈ y := by
  cases p
  simp only [pair, Part.mem_bind_iff, Part.mem_map_iff, Prod.mk.injEq]
  aesop

def pairing : Elgot.ParallelPairing Part where
  pair := pair
  natural f g x y := by
    apply Part.ext
    rintro ⟨c, d⟩
    simp only [Part.map_eq_map, Part.mem_map_iff, mem_pair]
    constructor
    · rintro ⟨⟨a, b⟩, h, e⟩
      exact ⟨⟨a, h.1, congrArg Prod.fst e⟩, ⟨b, h.2, congrArg Prod.snd e⟩⟩
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
  swap x y := by
    apply Part.ext
    rintro ⟨b, a⟩
    simp only [Part.map_eq_map, Part.mem_map_iff, mem_pair]
    constructor
    · rintro ⟨⟨a', b'⟩, h, e⟩
      cases e
      exact ⟨h.2, h.1⟩
    · intro h
      exact ⟨(a, b), ⟨h.2, h.1⟩, rfl⟩
  assoc x y z := by
    apply Part.ext
    rintro ⟨a, b, c⟩
    simp only [Part.map_eq_map, Part.mem_map_iff, mem_pair]
    constructor
    · rintro ⟨⟨⟨a', b'⟩, c'⟩, h, e⟩
      cases e
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro h
      exact ⟨((a, b), c), ⟨⟨h.1, h.2.1⟩, h.2.2⟩, rfl⟩
  rightUnit x := by
    apply Part.ext
    intro a
    simp only [Part.map_eq_map, Part.pure_eq_some, Part.mem_map_iff]
    constructor
    · rintro ⟨⟨a', b⟩, h, rfl⟩
      exact (mem_pair.mp h).1
    · intro h
      exact ⟨(a, PUnit.unit), mem_pair.mpr ⟨h, Part.mem_some _⟩, rfl⟩

def step : Bool → PUnit ⊕ Bool
  | false => .inr true
  | true => .inl PUnit.unit

def probe (available : Bool) : Part PUnit :=
  if available then Part.some PUnit.unit else Part.none

def ordinary : (f : Op) → IsPure false (Φ := source.Instr) f → Val (src f) → Val (trg f)
  | .step, _ => step
  | .probe, h => nomatch h

def execute (available : Bool) : (f : Op) → Val (src f) → Part (Val (trg f))
  | .step => fun b => pure (step b)
  | .probe => fun _ => probe available

theorem execute_pure (available : Bool) (f : Op) (h : IsPure false (Φ := source.Instr) f)
    (a : Val (src f)) : execute available f a = pure (ordinary f h a) := by
  cases f with
  | step => rfl
  | probe =>
      change true = false at h
      cases h

noncomputable def model (available : Bool) : Model target where
  Carrier := Part
  pairing := pairing
  instructions :=
    { denote := fun f => execute available (f.getD .probe)
      denotePure := fun f h => ordinary (f.getD .probe) h
      denote_pure := fun f => execute_pure available (f.getD .probe) }

theorem loop_returns (seed : Bool) :
    Elgot.iter (fun state => Part.some (step state)) seed = Part.some PUnit.unit := by
  apply Part.eq_some_iff.mpr
  apply (Elgot.Part.mem_iter_iff _ _ _).mpr
  cases seed
  · exact .more (a' := true) (Part.mem_some _) (.done (Part.mem_some _))
  · exact .done (Part.mem_some _)

theorem eval_lhs (available seed : Bool) :
    (model available).eval (equation.map addOpcode).lhs PUnit.unit (PUnit.unit, seed) =
      (probe available).map (fun z => (PUnit.unit, z)) := by
  change ((id : PUnit × PUnit → PUnit × PUnit) <$> pairing.pair
    ((pure seed : Part Bool) >>= Elgot.iter
      (fun s => ((pure s : Part Bool) >>= fun state =>
        (pure (step state) : Part (PUnit ⊕ Bool))) >>= pure))
    ((pure PUnit.unit : Part PUnit) >>= fun _ => probe available)) = _
  simp [Part.bind_some, loop_returns, pairing, pair]
  exact Part.map_id' (fun _ => rfl) _

theorem eval_rhs (available seed : Bool) :
    (model available).eval (equation.map addOpcode).rhs PUnit.unit (PUnit.unit, seed) =
      Part.some (PUnit.unit, PUnit.unit) := by
  change ((pure PUnit.unit : Part PUnit) >>= fun a =>
    (pure PUnit.unit : Part PUnit) >>= fun b => pure (a, b)) = _
  simp

theorem translated_true : Sat (model true) (equation.map addOpcode) := by
  rintro ⟨⟩ ⟨⟨⟩, seed⟩
  exact (eval_lhs true seed).trans (eval_rhs true seed).symm

theorem translated_false : ¬ Sat (model false) (equation.map addOpcode) := by
  intro h
  have hf := h PUnit.unit (PUnit.unit, false)
  have hnone := (eval_lhs false false).trans (Part.map_none _)
  exact Part.none_ne_some _ (hnone.symm.trans (hf.trans (eval_rhs false false)))

theorem reduct_true : Sat ((model true).reduct addOpcode) equation :=
  (satisfaction addOpcode (model true) equation).mp translated_true

theorem reduct_false : ¬ Sat ((model false).reduct addOpcode) equation :=
  fun h => translated_false ((satisfaction addOpcode (model false) equation).mpr h)

end LetParIterInstitution
