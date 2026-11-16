module

public import Silmaril.Logic.Consequence.Structural.Defs
import Silmaril.Proofs.Logic.Consequence.Structural.Closure

/-!
# Structural closures: leastness, closure operator, lattice of closed relations

* `Derives rs R` is closed under `rs` (`derives_closed`), contains `R` (`le_derives`), and is
  below every closed relation containing `R` (`derives_le`); hence monotone (`derives_mono`,
  also in the rules: `derives_mono_rules`) and idempotent (`derives_derives`).
* `closure rs` packages this as a Mathlib `ClosureOperator` whose closed elements are exactly
  the `Closed rs` relations (`isClosed_closure_iff`). Its closed elements `(closure rs).Closeds`
  form a complete lattice (`instCompleteLatticeCloseds`, meets are pointwise:
  `closed_sInf`), and `(closure rs).gi` is the Galois insertion `Derives rs ⊣ (↑)`
  (`derives_le_iff`: for closed `S`, `Derives rs R ≤ S ↔ R ≤ S`).
* Relations between the rules: `WeakSubset` gives `WeakSublist`, `Exchange` and `Contraction`;
  `WeakSubperm ↔ WeakSublist ∧ Exchange`. The converse fails in general: sublist weakening and
  exchange do not give contraction.
* Practical list API: `cut_single` (one cut, from reflexivity and multi-cut) and `cut_shared`
  (a shared context, which needs weakening along `⊆`: it contracts the copies of `Γ`).
-/

@[expose] public section

namespace Silmaril.Consequence.Structural

universe u

variable {C : Type u}

/-! ## Leastness -/

theorem le_derives (rs : Rules C) (R : Rel C) : R ≤ Derives rs R := fun _ _ => .base

theorem derives_closed (rs : Rules C) (R : Rel C) : Closed rs (Derives rs R) :=
  Proofs.Logic.Consequence.Structural.derives_closed rs R

theorem derives_le {rs : Rules C} {R S : Rel C} (hRS : R ≤ S) (hS : Closed rs S) :
    Derives rs R ≤ S :=
  Proofs.Logic.Consequence.Structural.derives_least hRS hS

theorem derives_le_iff {rs : Rules C} {R S : Rel C} (hS : Closed rs S) :
    Derives rs R ≤ S ↔ R ≤ S :=
  ⟨fun h => (le_derives rs R).trans h, fun h => derives_le h hS⟩

theorem derives_mono (rs : Rules C) {R S : Rel C} (h : R ≤ S) : Derives rs R ≤ Derives rs S :=
  derives_le (h.trans (le_derives rs S)) (derives_closed rs S)

theorem derives_mono_rules {rs rs' : Rules C} (hr : rs.refl → rs'.refl)
    (hw : rs.weak ≤ rs'.weak) (hc : rs.cut → rs'.cut) (R : Rel C) :
    Derives rs R ≤ Derives rs' R :=
  Proofs.Logic.Consequence.Structural.derives_mono_rules hr hw hc R

theorem closed_iff_derives_le {rs : Rules C} {R : Rel C} : Closed rs R ↔ Derives rs R ≤ R :=
  ⟨fun h => derives_le le_rfl h, fun h => ⟨fun hr _ _ hc => h _ _ (.refl hr hc),
    fun _ _ _ hw hd => h _ _ (.weak hw (.base hd)),
    fun hc _ _ hps hd => h _ _ (.cut _ hc (fun p hp => .base (hps p hp)) (.base hd))⟩⟩

theorem derives_eq_self {rs : Rules C} {R : Rel C} (h : Closed rs R) : Derives rs R = R :=
  le_antisymm (derives_le le_rfl h) (le_derives rs R)

theorem derives_derives (rs : Rules C) (R : Rel C) : Derives rs (Derives rs R) = Derives rs R :=
  derives_eq_self (derives_closed rs R)

/-- Closedness is preserved by arbitrary meets (pointwise conjunction). -/
theorem closed_sInf {rs : Rules C} (Rs : Set (Rel C)) (h : ∀ R ∈ Rs, Closed rs R) :
    Closed rs (sInf Rs) :=
  Proofs.Logic.Consequence.Structural.closed_inf Rs h

/-! ## Closure operator and the lattice of closed relations -/

/-- The structural closure as a Mathlib closure operator; its closed elements are the
`Closed rs` relations. -/
def closure (rs : Rules C) : ClosureOperator (Rel C) :=
  .ofPred (Derives rs) (Closed rs) (le_derives rs) (derives_closed rs)
    fun _ _ h hS => derives_le h hS

theorem closure_apply (rs : Rules C) (R : Rel C) : closure rs R = Derives rs R := rfl

theorem isClosed_closure_iff {rs : Rules C} {R : Rel C} : (closure rs).IsClosed R ↔ Closed rs R :=
  Iff.rfl

/-- Relations closed under `rs` form a complete lattice (lifted along the Galois insertion
`(closure rs).gi`: joins are closures of joins, meets are pointwise). -/
instance instCompleteLatticeCloseds (rs : Rules C) : CompleteLattice (closure rs).Closeds :=
  (closure rs).gi.liftCompleteLattice

/-- The closure adjunction: `Derives rs` is left adjoint to the inclusion of closed relations. -/
theorem gc_closure (rs : Rules C) : GaloisConnection (closure rs).toCloseds Subtype.val :=
  (closure rs).gi.gc

/-! ## Relations between rules -/

theorem WeakSubset.weakSublist {R : Rel C} (h : WeakSubset R) : WeakSublist R :=
  fun _ _ _ hs hd => h hs.subset hd

theorem WeakSubset.exchange {R : Rel C} (h : WeakSubset R) : Exchange R :=
  fun _ _ _ hp hd => h hp.subset hd

theorem WeakSubset.contraction {R : Rel C} (h : WeakSubset R) : Contraction R :=
  fun _ _ _ hd => h (by intro x; simp) hd

theorem weakSubperm_iff {R : Rel C} : WeakSubperm R ↔ WeakSublist R ∧ Exchange R :=
  Proofs.Logic.Consequence.Structural.weakSubperm_iff

/-! ## Practical cut rules -/

/-- One cut: `Γ ⊢ a` and `a :: Δ ⊢ c` give `Γ ++ Δ ⊢ c`, from reflexivity and multi-cut. -/
theorem cut_single {R : Rel C} (hr : Reflexive R) (hc : Cut R) {Γ Δ : List C} {a c : C}
    (ha : R Γ a) (hd : R (a :: Δ) c) : R (Γ ++ Δ) c :=
  Proofs.Logic.Consequence.Structural.cut_single hr hc ha hd

/-- Cut with a shared context: `Γ ⊢ a` for every `a ∈ cs` and `cs ⊢ c` give `Γ ⊢ c`. Needs
weakening along `⊆` (which contracts the copies of `Γ`). -/
theorem cut_shared {R : Rel C} (hc : Cut R) (hw : WeakSubset R) {Γ cs : List C} {c : C}
    (hcs : ∀ a ∈ cs, R Γ a) (hd : R cs c) : R Γ c :=
  Proofs.Logic.Consequence.Structural.cut_shared hc hw hcs hd

namespace Derives

variable {W : List C → List C → Prop} {R : Rel C}

/-- In the joint closure, a premise is derivable. -/
theorem of_mem {Γ : List C} {c : C} (h : c ∈ Γ) : Derives (jointRules W) R Γ c := .refl trivial h

/-- In the joint closure, weaken along the policy. -/
theorem weaken {Γ Δ : List C} {c : C} (hw : W Γ Δ) (h : Derives (jointRules W) R Γ c) :
    Derives (jointRules W) R Δ c := .weak hw h

/-- In the joint closure, one cut. -/
theorem cut1 {Γ Δ : List C} {a c : C} (ha : Derives (jointRules W) R Γ a)
    (hd : Derives (jointRules W) R (a :: Δ) c) : Derives (jointRules W) R (Γ ++ Δ) c :=
  cut_single (fun _ _ h => .refl trivial h) (fun _ _ hps hd => .cut _ trivial hps hd) ha hd

end Derives

end Silmaril.Consequence.Structural
