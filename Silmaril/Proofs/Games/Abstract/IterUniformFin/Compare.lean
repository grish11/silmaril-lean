module

public import Silmaril.Games.Abstract.IterUniformFin.Defs
public import Silmaril.Games.Abstract.IterUniform.Thms

/-!
# Finite branching against determinism (proofs)

* A silent, deterministic, trap-free, defined map has one behaviour at each state and argument,
  so it is finitely branching (`silentFinNoTrap_of_silentDetNoTrap`): the finitely branching
  theorem generalises `FullFun.iter_uniform_silent`.
* The nondeterministic counterexample `FullFun.not_iter_uniform_nondet` is silent, trap-free
  and defined, and it is **not** finitely branching: it returns any natural number
  (`not_iter_uniform_infinite`). So finite branching cannot be dropped either.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.IterUniformFin

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratOps

universe u

variable {E : Sig.{u}} {S A A' : Type u}

theorem silentFinNoTrap_of_silentDetNoTrap {h : FullFun E S A' A}
    (hh : FullFun.SilentDetNoTrap h) : FullFun.SilentFinNoTrap h := by
  refine ⟨hh.1, hh.2.2.1, hh.2.2.2, fun s a => ?_⟩
  rcases (FullFun.silentDetNoTrap_iff.1 hh s a).2 with he | ⟨x, t, he⟩ <;> rw [he] <;>
    exact Set.finite_singleton _

theorem silentFinNoTrapT_of_silentDetNoTrapT {t : ObsTriple E S A' A}
    (ht : SilentDetNoTrapT t) : SilentFinNoTrapT t :=
  ⟨ht.1, silentFinNoTrap_of_silentDetNoTrap ht.2⟩

theorem not_iter_uniform_infinite (E : Sig.{u}) :
    let h : FullFun E PUnit.{u + 1} PUnit.{u + 1} (ULift.{u} ℕ) :=
      (fun s _ => {y | ∃ n : ℕ, y = ([], End.ret ⟨n⟩ s)}, fun _ _ => ∅)
    let F : FullFun E PUnit.{u + 1} (ULift.{u} ℕ) (PUnit.{u + 1} ⊕ ULift.{u} ℕ) :=
      (fun s n => {y | y = ([], End.ret (.inl ⟨⟩) s) ∨
        ∃ m < n.down, y = ([], End.ret (.inr ⟨m⟩) s)}, fun _ _ => ∅)
    let G : FullFun E PUnit.{u + 1} PUnit.{u + 1} (PUnit.{u + 1} ⊕ PUnit.{u + 1}) :=
      (fun s _ => {y | y = ([], End.ret (.inl ⟨⟩) s) ∨ y = ([], End.ret (.inr ⟨⟩) s)},
        fun _ _ => ∅)
    FullFun.Silent h ∧ FullFun.NoTrap h ∧ FullFun.Defined h ∧ ¬ FullFun.FinBranch h ∧
      FullFun.seq h F = FullFun.seq G (FullFun.case (FullFun.pure.map Sum.inl) (h.map Sum.inr)) ∧
      ([], End.div) ∈ (FullFun.iter G).1 ⟨⟩ ⟨⟩ ∧
      ([], End.div) ∉ (FullFun.seq h (FullFun.iter F)).1 ⟨⟩ ⟨⟩ := by
  intro h F G
  obtain ⟨hs, hret, -, -, hyp, hG, hF⟩ := FullFun.not_iter_uniform_nondet E
  refine ⟨hs, fun s a ⟨c, hc⟩ => (hret s a).2 _ hc trivial, fun s a => (hret s a).1, ?_, hyp,
    hG, hF⟩
  intro hfin
  have hrange : h.1 ⟨⟩ ⟨⟩ =
      Set.range fun n : ℕ => (([] : List (Call E)), (End.ret ⟨n⟩ ⟨⟩ : End PUnit (ULift ℕ))) := by
    ext y
    exact ⟨fun ⟨n, hn⟩ => ⟨n, hn.symm⟩, fun ⟨n, hn⟩ => ⟨n, hn.symm⟩⟩
  have hinf := Set.infinite_range_of_injective (α := ℕ)
    (f := fun n : ℕ => (([] : List (Call E)), (End.ret ⟨n⟩ ⟨⟩ : End PUnit (ULift ℕ))))
    fun n m he => by
      injection he with _ he
      injection he with he
      exact congrArg ULift.down he
  exact hinf (hrange ▸ hfin ⟨⟩ ⟨⟩)

end Silmaril.Proofs.Games.Abstract.IterUniformFin
