module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Semantics.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.SSA.LambdaRTL
open LambdaSSA.Semantics (Env extend)
open LetCase.LocallyNameless (Tm)
open Silmaril.Isotope.Morphism.CaseSSA (erase)

universe u
variable {V K F α : Type u} {n labels : Nat}
variable (prim : F → Value α → Part (Value α))

private theorem evalValue (src : Val V) {names : Names V n} {target : Tm Empty F n}
    (compiled : value names src = some target)
    {store : V → Value α} {env : Env α} (agrees : Agrees names store env) (result : Value α) :
    LambdaSSA.Semantics.Tm.Eval (instr prim) env (erase target) () result () ↔
      result = src.eval (model prim) store := by
  induction src generalizing target result with
  | var reg =>
    obtain ⟨slot, found, rfl⟩ := Option.map_eq_some_iff.mp compiled
    constructor
    · intro h
      cases h
      exact agrees _ _ found
    · intro h
      exact .var_of_eq ((agrees _ _ found).trans h.symm)
  | unit =>
    cases compiled
    constructor
    · intro h
      cases h
      rfl
    · rintro rfl
      exact .unit
  | pair left right ihLeft ihRight =>
    simp only [value, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨a, ha, b, hb, rfl⟩ := compiled
    constructor
    · intro h
      cases h with
      | pair hl hr =>
        rw [(ihLeft ha _).mp hl, (ihRight hb _).mp hr]
        rfl
    · rintro rfl
      exact .pair ((ihLeft ha _).mpr rfl) ((ihRight hb _).mpr rfl)

private theorem evalOperand (src : Op V F) {names : Names V n} {target : Tm Empty F n}
    (compiled : operand names src = some target)
    {store : V → Value α} {env : Env α} (agrees : Agrees names store env) (result : Value α) :
    result ∈ src.eval (model prim) store ↔
      LambdaSSA.Semantics.Tm.Eval (instr prim) env (erase target) () result () := by
  cases src with
  | val v =>
    exact Part.mem_some_iff.trans (evalValue prim v compiled agrees result).symm
  | app f arg =>
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp compiled
    constructor
    · intro member
      exact .op ((evalValue prim arg ha agrees _).mpr rfl) member
    · intro h
      cases h with
      | op harg action =>
        cases (evalValue prim arg ha agrees _).mp harg
        exact action
  | inl | inr | abort => cases compiled

variable [DecidableEq V]

private theorem agrees_bind {names : Names V n} {store : V → Value α} {env : Env α}
    (agrees : Agrees names store env) (reg : V) (arg : Value α) :
    Agrees (bindName names reg) (upd store reg arg) (extend env arg) := by
  intro x i found
  by_cases same : x = reg
  · subst x
    have eq : i = 0 := by simpa [bindName] using found.symm
    subst i
    simp [upd]
  · simp only [bindName, ite_eq_right same, Option.map_eq_some_iff] at found
    obtain ⟨slot, old, rfl⟩ := found
    simpa [upd, same] using agrees x slot old

private theorem split_member (scrutinee : Value α) (tag : Value α ⊕ Value α) :
    tag ∈ (model prim).split scrutinee ↔
      scrutinee = Sum.elim Value.inl Value.inr tag := by
  cases tag <;> cases scrutinee <;> simp [model, Part.mem_some_iff, eq_comm]

private theorem unpair_member (arg : Value α) (pair : Value α × Value α) :
    pair ∈ (model prim).unpair arg ↔ arg = .pair pair.1 pair.2 := by
  rcases pair with ⟨a, b⟩
  cases arg <;> simp [model, Part.mem_some_iff, eq_comm]

private def output (label : K) (arg : Value α) (_ : V → Value α) : Part (K × Value α) :=
  Part.some (label, arg)

private theorem evalTerm (index : K → Option (Fin labels)) (src : CFG.Term V K F)
    {n : Nat} {names : Names V n} {target : LambdaSSA.Flat F labels n}
    (compiled : term index names src = some target)
    {store : V → Value α} {env : Env α} (agrees : Agrees names store env)
    (out : Nat) (result : Value α) :
    (out, result) ∈ (src.exec (model prim) output store >>= number index) ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) env target.erase () out result () := by
  induction src generalizing n names store env with
  | br label arg =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨i, numbered, a, ha, rfl⟩ := compiled
    simp only [CFG.Term.exec, output, Part.bind_eq_bind, Part.bind_some, number,
      numbered, Part.mem_some_iff, Prod.mk.injEq, LambdaSSA.Flat.erase]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact .br ((evalValue prim arg ha agrees _).mpr rfl)
    · intro h
      cases h with
      | br harg => exact ⟨rfl, (evalValue prim arg ha agrees _).mp harg⟩
  | case op x left y right ihLeft ihRight =>
    simp only [term, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨discr, hd, l, hl, r, hr, rfl⟩ := compiled
    simp only [CFG.Term.exec, LambdaSSA.Flat.erase, Part.bind_eq_bind, Part.bind_assoc, Part.mem_bind_iff]
    constructor
    · rintro ⟨scrutinee, hscrutinee, tag, htag, next⟩
      cases tag with
      | inl a =>
        cases (split_member prim _ _).mp htag
        exact .case_inl ((evalOperand prim op hd agrees _).mp hscrutinee)
          ((ihLeft hl (agrees_bind agrees x a)).mp (Part.mem_bind_iff.mpr next))
      | inr b =>
        cases (split_member prim _ _).mp htag
        exact .case_inr ((evalOperand prim op hd agrees _).mp hscrutinee)
          ((ihRight hr (agrees_bind agrees y b)).mp (Part.mem_bind_iff.mpr next))
    · intro h
      cases h with
      | case_inl discr next =>
        exact ⟨_, (evalOperand prim op hd agrees _).mpr discr, .inl _,
          (split_member prim _ _).mpr rfl,
          Part.mem_bind_iff.mp ((ihLeft hl (agrees_bind agrees x _)).mpr next)⟩
      | case_inr discr next =>
        exact ⟨_, (evalOperand prim op hd agrees _).mpr discr, .inr _,
          (split_member prim _ _).mpr rfl,
          Part.mem_bind_iff.mp ((ihRight hr (agrees_bind agrees y _)).mpr next)⟩

theorem evalBody (index : K → Option (Fin labels)) (src : CFG.Body V K F)
    {n : Nat} {names : Names V n} {target : LambdaSSA.Flat F labels n}
    (compiled : body index names src = some target)
    {store : V → Value α} {env : Env α} (agrees : Agrees names store env)
    (out : Nat) (result : Value α) :
    (out, result) ∈ (src.evalJump (model prim) store >>= number index) ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) env target.erase () out result () := by
  induction src generalizing n names store env with
  | term tail => exact evalTerm prim index tail compiled agrees out result
  | let1 x op rest ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨arg, ha, code, hc, rfl⟩ := compiled
    simp only [CFG.Body.evalJump, CFG.Body.exec, LambdaSSA.Flat.erase, Part.bind_eq_bind,
      Part.bind_assoc]
    rw [Part.mem_bind_iff]
    constructor
    · rintro ⟨a, ha', next⟩
      exact .let₁ ((evalOperand prim op ha agrees _).mp ha')
        ((ih hc (agrees_bind agrees x a)).mp next)
    · intro h
      cases h with
      | let₁ arg next =>
        exact ⟨_, (evalOperand prim op ha agrees _).mpr arg,
          (ih hc (agrees_bind agrees x _)).mpr next⟩
  | let2 x y op rest ih =>
    simp only [body, Option.bind_eq_some_iff, Option.map_eq_some_iff] at compiled
    obtain ⟨arg, ha, code, hc, rfl⟩ := compiled
    simp only [CFG.Body.evalJump, CFG.Body.exec, LambdaSSA.Flat.erase, Part.bind_eq_bind,
      Part.bind_assoc]
    rw [Part.mem_bind_iff]
    constructor
    · rintro ⟨a, ha', follow⟩
      obtain ⟨⟨left, right⟩, unpacked, next⟩ := Part.mem_bind_iff.mp follow
      cases (unpair_member prim _ _).mp unpacked
      exact .let₂ ((evalOperand prim op ha agrees _).mp ha')
        ((ih hc (agrees_bind (agrees_bind agrees x left) y right)).mp next)
    · intro h
      cases h with
      | let₂ arg next =>
        rename_i middle left right
        cases middle
        exact ⟨_, (evalOperand prim op ha agrees _).mpr arg,
          Part.mem_bind ((unpair_member prim _ (left, right)).mpr rfl)
            ((ih hc (agrees_bind (agrees_bind agrees x left) y right)).mpr next)⟩

omit [DecidableEq V] in
private theorem tabulate_at {A : Type u} {count : Nat} {f : Fin count → Option A}
    {table : Fin count → A} (elaborated : tabulate count f = some table) (i : Fin count) :
    f i = some (table i) := by
  induction count with
  | zero => exact i.elim0
  | succ count ih =>
    simp only [tabulate, Option.bind_eq_some_iff, Option.map_eq_some_iff] at elaborated
    obtain ⟨head, hhead, rest, hrest, rfl⟩ := elaborated
    exact Fin.cases hhead (fun j => ih hrest j) i

variable [DecidableEq K]

theorem entry_iff (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (store : V → Value α) (env : Env α)
    (inputs : ∀ i : Fin n, env i.val = store (captures i)) (out : Nat) (result : Value α) :
    (out, result) ∈ (graph.entry.evalJump (model prim) store >>= number (labelIndex graph.blocks exits)) ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) env target.entry.erase () out result () := by
  simp only [elaborate, Option.bind_eq_some_iff, Option.map_eq_some_iff] at accepted
  obtain ⟨entry, compiled, blocks, _, rfl⟩ := accepted
  apply evalBody prim _ _ compiled _ out result
  intro name slot found
  unfold first at found
  have eq : captures slot = name :=
    of_decide_eq_true (List.find?_some (p := fun i : Fin n => decide (captures i = name)) found)
  simpa [eq] using inputs slot

theorem block_iff (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (i : Fin graph.blocks.length) (store : V → Value α) (env : Env α)
    (payload : Value α) (out : Nat) (result : Value α) :
    (out, result) ∈ (graph.blocks[i].2.body.evalJump (model prim)
      (upd store graph.blocks[i].2.param payload) >>= number (labelIndex graph.blocks exits)) ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) (extend env payload)
        (target.block i).erase () out result () := by
  simp only [elaborate, Option.bind_eq_some_iff, Option.map_eq_some_iff] at accepted
  obtain ⟨entry, _, blocks, compiled, rfl⟩ := accepted
  apply evalBody prim _ _ (tabulate_at compiled i) _ out result
  have hidden : Agrees (fun (_ : V) => (none : Option (Fin n))) store env := by
    intro _ _ impossible
    cases impossible
  exact agrees_bind hidden _ payload

omit [DecidableEq V] in
theorem lookup_index (blocks : List (K × CFG.Block V K F)) (label : K) :
    blocks.lookup label = (blocks.findFinIdx? (fun item => label == item.1)).map
      (fun i => blocks[i].2) := by
  induction blocks with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨key, block⟩
    simp only [List.lookup_cons, List.findFinIdx?_cons]
    cases label == key with
    | true => simp
    | false => simp [ih, Option.map_map, Function.comp_def]

theorem step_iff (graph : CFG V K F) (exits : List K) (captures : Fin n → V)
    {target : LambdaSSA.FiniteCFG F graph.blocks.length exits.length n}
    (accepted : elaborate graph exits captures = some target)
    (label : K) (i : Fin graph.blocks.length)
    (hit : graph.blocks.findFinIdx? (fun item => label == item.1) = some i)
    (store : V → Value α) (env : Env α) (payload : Value α) (out : Nat) (result : Value α) :
    (out, result) ∈ (CFG.Cyclic.stepSSA (model prim) graph.blocks store (label, payload) >>=
      Sum.elim (fun _ => Part.none) (number (labelIndex graph.blocks exits))) ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) (extend env payload)
        (target.block i).erase () out result () := by
  have found : graph.blocks.lookup label = some graph.blocks[i].2 := by
    rw [lookup_index, hit]
    rfl
  simp only [CFG.Cyclic.stepSSA, found, ← bind_pure_comp, bind_assoc, pure_bind, Sum.elim_inr]
  exact block_iff prim graph exits captures accepted i store env payload out result

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat
