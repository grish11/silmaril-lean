module

public import Silmaril.Wasm.Execution.Core.GlobalProfile.Defs
import Silmaril.Wasm.Execution.Core.Entry.Thms
import Silmaril.Wasm.Execution.Core.Entry.Determinism.Thms
import Silmaril.Wasm.Execution.Core.Intrinsic.Normalize.Thms
import Silmaril.Wasm.Behaviour.Refinement.Interpreter
import Silmaril.Wasm.Cfg.ProfileFree.Thms

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.GlobalProfile

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Execution.Core.GlobalProfile
open Silmaril.Wasm.Execution.Core.Intrinsic (Values stackTypes observeResult)
open Silmaril.Wasm.Execution.Core.Entry Silmaril.Wasm.Validation Silmaril.Wasm.Numerics
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.SingleThreaded.Det Silmaril.Wasm.Cfg.ProfileFree
  Silmaril.Wasm.SingleThreaded.Exec.BehaviourRefinement Silmaril.Semantics.Operational

variable {P : Profile} {mutability : Mutability} {input output : List IntType}

private theorem context_step {value next : BitVec 32} {left right : List Admin}
    (edge : Step P noHost (config mutability value left) (config mutability next right))
    (saved : List Val) (rest : List Admin) :
    Step P noHost (config mutability value (vals saved ++ left ++ rest))
      (config mutability next (vals saved ++ right ++ rest)) := by
  by_cases extra : saved ≠ [] ∨ rest ≠ []
  · exact .ctxtInstrs edge extra
  · have ⟨first, second⟩ := not_or.mp extra
    rw [of_not_not first, of_not_not second]
    simpa using edge

private theorem bubble {value : BitVec 32} (saved : List Val) (rest : List Admin) :
    Steps P noHost (config mutability value (vals saved ++ [.trap] ++ rest)) (config mutability value [.trap]) := by
  by_cases extra : saved ≠ [] ∨ rest ≠ []
  · exact .single (.trapInstrs extra)
  · have ⟨first, second⟩ := not_or.mp extra
    rw [of_not_not first, of_not_not second]
    exact .refl

theorem eval_finishes (code : Code mutability input output) (stack : Values input) (value : BitVec 32) :
    Finishes P noHost (code.start stack value) ((code.eval stack value).erase mutability)
      (code.eval stack value).result := by
  refine ⟨?_, rfl⟩
  induction code generalizing value with
  | done => simpa [Code.start, Code.erase, Code.eval, Answer.erase, Result.toAdmin] using
      (show Steps P noHost (config _ value (vals stack.erase.reverse)) _ from .refl)
  | const bits tail ih =>
    simpa [Code.start, Code.erase, Code.eval, Values.erase, List.append_assoc, vals, Val.i32] using
      ih (.cons (kind := .i32) bits stack) value
  | @get kind saved results tail ih =>
    have edge : Step P noHost (config kind value [get]) (config kind value [(Val.i32 value).toAdmin]) :=
      .variable (.globalGet (a := 0) (g := global kind value) rfl)
    have suffix := ih (.cons (kind := .i32) value stack) value
    simp only [Code.start, Values.erase, List.reverse_cons, vals_append, List.append_assoc] at suffix
    have steps := (Relation.ReflTransGen.single (context_step edge stack.erase.reverse tail.erase)).trans
      (by simpa [vals, Val.i32, List.append_assoc] using suffix)
    simpa [Code.start, Code.erase, Code.eval] using steps
  | set tail ih =>
    cases stack with
    | cons bits stack =>
      have edge : Step P noHost (config .var value [(Val.i32 bits).toAdmin, set]) (config .var bits []) :=
        .variable (.globalSet (a := 0) (g := global .var value) rfl)
      have path := Relation.ReflTransGen.single (context_step edge stack.erase.reverse tail.erase)
      exact (by simpa [Code.start, Code.erase, Code.eval, Values.erase, List.append_assoc, vals, Val.i32] using
        path.trans (by simpa [Code.start] using ih stack bits))
  | @bin kind saved results op tail ih =>
    cases stack with
    | cons rhs stack =>
      cases stack with
      | cons lhs stack =>
        cases eqn : intBinOp .i32 op lhs rhs with
        | ok bits =>
          have edge : Step P noHost (config kind value [(Val.i32 lhs).toAdmin, (Val.i32 rhs).toAdmin, bin op])
              (config kind value [(Val.i32 bits).toAdmin]) := .numeric (.intBinOp eqn)
          have path := Relation.ReflTransGen.single (context_step edge stack.erase.reverse tail.erase)
          have suffix := ih (.cons (kind := .i32) bits stack) value
          simp only [Code.start, Values.erase, List.reverse_cons, vals_append, List.append_assoc] at suffix
          have steps := path.trans (by simpa [vals, Val.i32, List.append_assoc] using suffix)
          simpa [Code.start, Code.erase, Code.eval, Values.erase, List.append_assoc, vals, Val.i32, eqn] using steps
        | error failure =>
          have edge : Step P noHost (config kind value [(Val.i32 lhs).toAdmin, (Val.i32 rhs).toAdmin, bin op])
              (config kind value [.trap]) := .numeric (.intBinOpTrap eqn)
          have path := (Relation.ReflTransGen.single (context_step edge stack.erase.reverse tail.erase)).trans
            (bubble (P := P) (mutability := kind) (value := value) stack.erase.reverse tail.erase)
          simpa [Code.start, Code.erase, Code.eval, Answer.erase, Result.toAdmin, Values.erase, List.append_assoc,
            vals, Val.i32, eqn] using path

private theorem integerTypes_ok (ctx : Context) (kinds : List IntType) : ResultOk ctx.toTypeCtx (stackTypes kinds) := by
  intro t member
  simp only [stackTypes, List.mem_reverse, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  exact .num _

private theorem sequence {s : Store Empty} {ctx : Context} {left right : List Admin}
    {params middle results : List CValType}
    (first : AdminsOk s ctx left (.plain params middle))
    (last : AdminsOk s ctx right (.plain middle results)) :
    AdminsOk s ctx (left ++ right) (.plain params results) := .seq first (by simp) last

private theorem with_stack {s : Store Empty} {ctx : Context} {instruction : Admin} {params results : List CValType}
    (head : AdminOk s ctx instruction (.plain params results)) (kinds : List IntType) :
    AdminsOk s ctx [instruction] (.plain (stackTypes kinds ++ params) (stackTypes kinds ++ results)) :=
  .frame (.single head) (integerTypes_ok ctx kinds)

private theorem code_ok (value : BitVec 32) (code : Code mutability input output) :
    AdminsOk (store mutability value) (context mutability) code.erase (.plain (stackTypes input) (stackTypes output)) := by
  induction code with
  | done => exact .id (integerTypes_ok _ _)
  | @const kind saved results bits tail ih =>
    have head : AdminOk (store kind value) (context kind) (Val.i32 bits).toAdmin (.plain [] [Ty.i32]) :=
      .plain (.numeric (.intConst .i32 bits))
    exact sequence (by simpa [stackTypes, Ty.i32] using with_stack head saved) ih
  | @get kind saved results tail ih =>
    have head : AdminOk (store kind value) (context kind) get (.plain [] [Ty.i32]) :=
      .plain (.variable (.globalGet (m := kind) rfl))
    exact sequence (by simpa [stackTypes, Ty.i32] using with_stack head saved) ih
  | @set saved results tail ih =>
    simp only [Code.erase]
    have head : AdminOk (store .var value) (context .var) set (.plain [Ty.i32] []) :=
      .plain (.variable (.globalSet rfl))
    have shifted : AdminsOk (store .var value) (context .var) [set]
        (.plain (stackTypes (.i32 :: saved)) (stackTypes saved)) := by
      simpa [stackTypes, Ty.i32] using with_stack head saved
    exact sequence shifted ih
  | @bin kind saved results op tail ih =>
    simp only [Code.erase]
    have head : AdminOk (store kind value) (context kind) (bin op) (.plain [Ty.i32, Ty.i32] [Ty.i32]) :=
      .plain (.numeric (.intBinOp .i32 op))
    have shifted : AdminsOk (store kind value) (context kind) [bin op]
        (.plain (stackTypes (.i32 :: .i32 :: saved)) (stackTypes (.i32 :: saved))) := by
      simpa [stackTypes, Ty.i32, List.append_assoc] using with_stack head saved
    exact sequence shifted ih

private theorem stack_ok (s : Store Empty) (ctx : Context) (stack : Values input) :
    AdminsOk s ctx (vals stack.erase.reverse) (.plain [] (stackTypes input)) := by
  induction stack with
  | nil => exact .nil
  | @cons kind saved bits tail ih =>
    have head : AdminOk s ctx (.plain (.intConst kind bits)) (.plain [] [.num (.int kind)]) :=
      .plain (.numeric (.intConst kind bits))
    have shift : AdminsOk s ctx [.plain (.intConst kind bits)]
        (.plain (stackTypes saved) (stackTypes (kind :: saved))) := by
      simpa [stackTypes] using with_stack head saved
    simpa [Values.erase, vals, Val.toAdmin] using sequence ih shift

theorem start_typed (code : Code mutability input output) (stack : Values input) (value : BitVec 32) :
    ConfigOk (code.start stack value) (stackTypes output) := by
  have globalOk : GlobalInstOk (store mutability value) (global mutability value) := ⟨.num _, .num _⟩
  have storeOk : StoreOk (store mutability value) := by
    constructor <;> simp [store]
    exact globalOk
  have moduleOk : ModuleInstOk (store mutability value) frame.module (context mutability) :=
    ModuleInstOk.mk (k := 0) (by simp [frame]) .nil
      (.cons (.global (gi := global mutability value) rfl) .nil) .nil .nil .nil (by simp [frame]) .nil
      (by simp [frame]) (by simp [frame]) (by simp [frame]) (by simp [frame])
  exact ⟨context mutability, ⟨storeOk, context mutability, [], moduleOk, .nil, rfl⟩,
    sequence (stack_ok _ _ stack) (code_ok value code)⟩

private theorem stack_free (stack : Values input) : ∀ instruction ∈ vals stack.erase.reverse, AFree instruction := by
  induction stack with
  | nil => simp [Values.erase, vals]
  | cons bits tail ih =>
    intro instruction member
    rw [Values.erase, List.reverse_cons, vals_append] at member
    rcases List.mem_append.mp member with saved | current
    · exact ih instruction saved
    · have eqn := List.mem_singleton.mp current
      subst instruction
      exact .plain (.atom id id)

private theorem code_free (code : Code mutability input output) : ∀ instruction ∈ code.erase, AFree instruction := by
  induction code with
  | done => simp [Code.erase]
  | const bits tail ih =>
    intro instruction member
    rcases List.mem_cons.mp (by simpa only [Code.erase] using member) with rfl | rest
    · exact .plain (.atom id id)
    · exact ih instruction rest
  | get tail ih =>
    intro instruction member
    rcases List.mem_cons.mp (by simpa only [Code.erase] using member) with rfl | rest
    · exact .plain (.atom id id)
    · exact ih instruction rest
  | set tail ih =>
    intro instruction member
    rcases List.mem_cons.mp (by simpa only [Code.erase] using member) with rfl | rest
    · exact .plain (.atom id id)
    · exact ih instruction rest
  | bin op tail ih =>
    intro instruction member
    rcases List.mem_cons.mp (by simpa only [Code.erase] using member) with rfl | rest
    · exact .plain (.atom id id)
    · exact ih instruction rest

private theorem start_free (code : Code mutability input output) (stack : Values input) (value : BitVec 32) :
    ConfigFree (code.start stack value) := by
  refine ⟨?_, by simp [FuncsFree, Code.start, config, store]⟩
  intro instruction member
  rcases List.mem_append.mp member with saved | tape
  · exact stack_free stack instruction saved
  · exact code_free code instruction tape

theorem finishes_iff (code : Code mutability input output) (stack : Values input) (value : BitVec 32)
    (final : Config Empty) (result : Result) : Finishes P noHost (code.start stack value) final result ↔
      final = (code.eval stack value).erase mutability ∧ result = (code.eval stack value).result := by
  constructor
  · intro run
    have computed := eval_finishes (P := profile neverFail) code stack value
    have transferred : Finishes (profile neverFail) noHost (code.start stack value) final result :=
      ⟨profileFree_steps (start_free code stack value) run.1, run.2⟩
    exact Entry.finishes_unique transferred computed
  · rintro ⟨rfl, rfl⟩
    exact eval_finishes code stack value

theorem safe_and_may (code : Code mutability input output) (stack : Values input) (value : BitVec 32) :
    (policy P noHost (stackTypes output)).SafeAt (code.start stack value) ∧
      ∀ outcome, (policy P noHost (stackTypes output)).toOpSem.May (code.start stack value) outcome ↔
        outcome = observeResult (code.eval stack value).result := by
  obtain ⟨safe, same⟩ := policy_safe_and_may (P := P) (host := noHost)
    (fun {_ _} => noHost_preserves) (start_typed code stack value)
  refine ⟨safe, fun outcome => (same outcome).trans (ordinary_may.trans ?_)⟩
  constructor
  · rintro ⟨final, result, run, rfl⟩
    rw [(finishes_iff code stack value final result |>.mp run).2]
  · rintro rfl
    exact ⟨_, _, eval_finishes code stack value, rfl⟩

theorem not_diverges (code : Code mutability input output) (stack : Values input) (value : BitVec 32) :
    ¬ Diverges P noHost (code.start stack value) := by
  intro diverges
  obtain ⟨trace, first, edges⟩ := diverges
  have free : ∀ count, ConfigFree (trace count) := by
    intro count
    induction count with
    | zero => exact first.symm ▸ start_free code stack value
    | succ count prev =>
      have ⟨funcs, instructions⟩ := step_free (edges count) (fun _ _ _ _ _ bad => bad.elim) prev.2 prev.1
      exact ⟨instructions, funcs⟩
  have transferred : Diverges (profile neverFail) noHost (code.start stack value) :=
    ⟨trace, first, fun count => step_profile (edges count) (free count).1⟩
  have done := eval_finishes (P := profile neverFail) code stack value
  exact Intrinsic.noHost_not_diverges_of_normal_form done.1
    (fun _ => not_step_of_terminal ⟨_, done.2⟩) transferred

end Silmaril.Proofs.Wasm.Execution.Core.GlobalProfile
