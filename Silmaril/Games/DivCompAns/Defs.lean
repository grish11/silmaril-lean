module

public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.DivLTS.Defs
import Silmaril.Proofs.Games.DivCompAns.Zip

/-!
# Composition seen through the answers of the lower component

In `σ.comp τ` (`σ : DStrategy E F` below, `τ : DStrategy F G` above), every answer that `τ`
receives at `F` is an answer that `σ` gives there: the two plays synchronise on `F`. So if `σ`
only gives answers in a set `R`, the composite only sees the part of `τ` whose answers at `F` are
in `R`. This module states that part and the transport of interactions to it.

* `LAnsIn R s`: every answer **below** (`.inl (.ans m n)`) in the move list `s` satisfies `R m n`;
  `RAnsIn R s`: every answer **above** (`.inr (.ans m n)`) does.
* `Prog.AllRet P p`: every return value of the program `p` satisfies `P`.
* `DStrategy.AnswersIn R σ`: every answer `σ` gives above satisfies `R`.
* `DStrategy.AnsPart R τ' τ`: `τ'` is the `R`-answered part of `τ`: `τ' ≤ τ`, and every play,
  divergence and infinite play of `τ` all of whose answers below satisfy `R` is one of `τ'`.
* `InfInteraction.ansRight`, `InfInteraction.ansLeft`: **coherent lifts** of an infinite
  interaction to the `R`-answered part, with the **same** chains of plays (the same lower, upper
  and visible stages): a single coherent infinite interaction, not a choice of finite preimages
  of prefixes. `InfInteraction.ofLe` is the converse transport, along refinement.

Theorems in `Silmaril.Games.DivCompAns.Thms`: `comp_eq_of_ansPart` (an `R`-answering `σ` composes
equally with `τ` and with its `R`-answered part, on finite plays, divergences including hidden
chatter, and infinite plays), `ansPart_comp` (the `R`-answered part is preserved by composing
above), `answersIn_ofHandler`.
-/

@[expose] public section

namespace Silmaril.Games

open Silmaril.Proofs.Games.DivCompAns (zip_inl_mem_left zip_inl_mem_right)

universe u

variable {E F G : Sig.{u}}

/-- Every answer below in `s` satisfies `R`. -/
def LAnsIn (R : (m : E.Op) → E.Ar m → Prop) (s : List (Move E F)) : Prop :=
  ∀ m n, (Sum.inl (Ev.ans m n) : Move E F) ∈ s → R m n

/-- Every answer above in `s` satisfies `R`. -/
def RAnsIn (R : (m : F.Op) → F.Ar m → Prop) (s : List (Move E F)) : Prop :=
  ∀ m n, (Sum.inr (Ev.ans m n) : Move E F) ∈ s → R m n

/-- Every return value of the program satisfies `P`. -/
def Prog.AllRet {A : Type u} (P : A → Prop) : Prog E A → Prop
  | .pure a => P a
  | .call _ k => ∀ n, (k n).AllRet P

namespace DStrategy

/-- **`σ` answers in `R`**: every answer `σ` gives above satisfies `R`. -/
def AnswersIn (R : (m : F.Op) → F.Ar m → Prop) (σ : DStrategy E F) : Prop :=
  ∀ s ∈ σ.toStrategy, RAnsIn R s

/-- **`τ'` is the `R`-answered part of `τ`**: it refines `τ` and has every play, divergence and
infinite play of `τ` whose answers below satisfy `R`. -/
def AnsPart (R : (m : E.Op) → E.Ar m → Prop) (τ' τ : DStrategy E F) : Prop :=
  τ' ≤ τ ∧ (∀ t ∈ τ.toStrategy, LAnsIn R t → t ∈ τ'.toStrategy) ∧
    (∀ t ∈ τ.div, LAnsIn R t → t ∈ τ'.div) ∧
    (∀ J ∈ τ.inf, (∀ t ∈ J, LAnsIn R t) → J ∈ τ'.inf)

/-- **Coherent lift on the right**: an infinite interaction of an `R`-answering `σ` with `τ` is
one with the `R`-answered part `τ'` of `τ`, with the same chains. -/
def InfInteraction.ansRight {R : (m : F.Op) → F.Ar m → Prop} {σ : DStrategy E F}
    {τ' τ : DStrategy F G} (hσ : σ.AnswersIn R) (h : τ'.AnsPart R τ) (i : InfInteraction σ τ) :
    InfInteraction σ τ' :=
  { i with
    mem_t := fun n => h.2.1 _ (i.mem_t n) fun _ _ hx => by
      exact hσ _ (i.mem_s n) _ _ (zip_inl_mem_right (i.zip n) hx)
    lim_t := fun hu => h.2.2.2 _ (i.lim_t hu) fun _ ⟨n, hq⟩ _ _ hx => by
      exact hσ _ (i.mem_s n) _ _ (zip_inl_mem_right (i.zip n) (hq.subset hx)) }

/-- **Coherent lift on the left**: an infinite interaction of `τ` with `ρ` whose visible stages
answer below in `R` is one of the `R`-answered part `τ'` of `τ` with `ρ`, with the same chains. -/
def InfInteraction.ansLeft {R : (m : E.Op) → E.Ar m → Prop} {τ' τ : DStrategy E F}
    {ρ : DStrategy F G} (h : τ'.AnsPart R τ) (i : InfInteraction τ ρ)
    (hp : ∀ n, LAnsIn R (i.p n)) : InfInteraction τ' ρ :=
  { i with
    mem_s := fun n => h.2.1 _ (i.mem_s n) fun _ _ hx => by
      exact hp n _ _ (zip_inl_mem_left (i.zip n) hx)
    lim_s := fun hu => h.2.2.2 _ (i.lim_s hu) fun _ ⟨n, hq⟩ _ _ hx => by
      exact hp n _ _ (zip_inl_mem_left (i.zip n) (hq.subset hx)) }

/-- **Transport along refinement**: an infinite interaction of `σ` with `τ` is one of any
refinements `σ₁ ≥ σ`, `τ₁ ≥ τ`, with the same chains (the converse direction of the lifts). -/
def InfInteraction.ofLe {σ σ₁ : DStrategy E F} {τ τ₁ : DStrategy F G} (hσ : σ ≤ σ₁)
    (hτ : τ ≤ τ₁) (i : InfInteraction σ τ) : InfInteraction σ₁ τ₁ :=
  { i with
    mem_s := fun n => hσ.1 (i.mem_s n)
    mem_t := fun n => hτ.1 (i.mem_t n)
    lim_s := fun hu => hσ.2.2 (i.lim_s hu)
    lim_t := fun hu => hτ.2.2 (i.lim_t hu) }

end DStrategy

end Silmaril.Games
