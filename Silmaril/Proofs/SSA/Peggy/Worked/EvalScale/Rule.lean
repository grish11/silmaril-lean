module

public import Silmaril.SSA.Peggy.Worked.EvalScale.Defs
import Silmaril.SSA.PEG.Rules.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.Worked.EvalScale

open Silmaril.SSA.PEG
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params} {values : g.Valuation m}
variable {op : P [.count, .count] .count}

set_option backward.isDefEq.respectTransparency false in
theorem binary_at (solves : g.Solves m env values) {r a b : Ref g.sort .count}
    (node : Rules.HasNode r (.op op) (.cons a (.cons b .nil))) (i : Index l) :
    Rules.readRef values r i = (Rules.readRef values a i).bind fun left =>
      (Rules.readRef values b i).bind fun right => m.run op (.cons left (.cons right .nil)) := by
  rw [Rules.at_label solves node i]
  have readFirst : (Tuple.cons a (.cons b .nil)).get
      (portAt ([.count, .count] : List (Ty Data)) 0) = a := rfl
  have readSecond : (Tuple.cons a (.cons b .nil)).get
      (portAt ([.count, .count] : List (Ty Data)) (Fin.succ (0 : Fin 1))) = b := rfl
  simp only [Label.interpret, collect, readFirst, readSecond]
  cases Rules.readRef values a i <;> cases Rules.readRef values b i <;> rfl

/-- Strict mapping commutes with the prefix test when it preserves definedness. -/
theorem monotonize_bind_of_total {A B : Type x} (s : Nat → Option A) (f : A → Option B)
    (total : ∀ a, (f a).isSome) (k : Nat) :
    (monotonize s k).bind f = monotonize (fun j => (s j).bind f) k := by
  have defined (j : Nat) : ((s j).bind f).isSome = (s j).isSome := by
    cases s j with
    | none => rfl
    | some a => exact total a
  have prefixDefined : (∀ j : Fin k, ((s j.val).bind f).isSome) ↔
      (∀ j : Fin k, (s j.val).isSome) := by simp only [defined]
  by_cases all : ∀ j : Fin k, (s j.val).isSome
  · simp [monotonize, all, prefixDefined.mpr all]
  · have bad : ¬∀ j : Fin k, ((s j.val).bind f).isSome := fun h => all (prefixDefined.mp h)
    simp [monotonize, all, bad]

/-- Appendix A.1 push-through-eval for a fixed defined left operand
and a binary operation total at that operand. -/
theorem commute (solves : g.Solves m env values)
    {outer sampled inner target a stream count : Ref g.sort .count} {loop : Fin l}
    (src : Rules.HasNode outer (.op op) (.cons a (.cons sampled .nil)))
    (sample : Rules.HasNode sampled (.eval loop) (.cons stream (.cons count .nil)))
    (product : Rules.HasNode inner (.op op) (.cons a (.cons stream .nil)))
    (dst : Rules.HasNode target (.eval loop) (.cons inner (.cons count .nil)))
    (k : m.Value .count) (constant : ∀ i, Rules.readRef values a i = some k)
    (total : ∀ b : m.Value .count, (m.run op (.cons k (.cons b .nil))).isSome) :
    Rules.StreamEq values outer target := by
  intro i
  rw [binary_at solves src i, constant i, Rules.eval_at solves sample i, Rules.eval_at solves dst i]
  cases Rules.readRef values count i with
  | none => rfl
  | some index =>
    let s := fun j => Rules.readRef values stream (i.set loop j)
    let f := fun b : m.Value .count => m.run op (.cons k (.cons b .nil))
    change (monotonize s index.down).bind f =
      monotonize (fun j => Rules.readRef values inner (i.set loop j)) index.down
    rw [monotonize_bind_of_total s f total]
    congr 1
    funext j
    rw [binary_at solves product, constant]
    rfl

end Silmaril.Proofs.SSA.Peggy.Worked.EvalScale
