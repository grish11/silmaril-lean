module

public import Silmaril.Proofs.Wasm.Interp.OracleSim
public import Silmaril.Proofs.Wasm.Interp.EHExt
public import Silmaril.Wasm.Abstract.CallXE.Defs
import Silmaril.Wasm.Cfg.Region.Thms

/-!
# Forward simulation with exceptions (F5, proofs)

With the exception checker `ehExt tags` and exceptions on (`eh = true`), every `EvalOXE C` run of
checked code without the extended call forms (`xFreeL`) is a Core 3.0 run (`evalOXE_goodEH`):

* `throw x` allocates the exception with the tag's fields and throws it (`Step.throw`);
* `throw_ref` traps on null and throws an exception reference;
* `try_table bt cs body` runs its body in `HANDLER_n{cs} LABEL_n{} …`: values and branches leave
  the label and the handler, and a thrown exception is resolved by the clauses with the existing
  first-match resolution `Cfg.Region.Catches` (`catches_steps`): a branch from outside the
  `try_table` with the clause's values, or a rethrow;
* calls answered by the oracle may throw (`OracleThrowsE`).

The arity side needs two run invariants (`TagsOk`): the store's tag instances are the `tags` the
checker reads, and every allocated exception has its tag's field count (`ExnsOk`), so a caught
exception pushes what the clause's label expects (`catches_count`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXE

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## The exception invariants -/

/-- Every exception of the store has its tag's field count, read by any instance naming its tag. -/
def ExnsOk (tags : List TagInst) (s : Store H) : Prop :=
  ∀ (a : Nat) (e : ExnInst), s.exns[a]? = some e → ∀ (mi : ModuleInst) (x : TagIdx),
    mi.tags[x.toNat]? = some e.tag → tagFields tags mi x = some e.fields.length

/-- The tag invariants of a run: the store's tags are `tags` and its exceptions are well formed. -/
def TagsOk (tags : List TagInst) (s : Store H) : Prop := s.tags = tags ∧ ExnsOk tags s

/-- **A tag-preserving oracle**: its answers keep the tag invariants. -/
def OracleTagsE (tags : List TagInst) (C : Abstract.CallRel H) : Prop :=
  ∀ (s s₂ : Store H) (a : Nat) (us : List Val) (fl : Binaryen.Flow),
    C s a us (s₂, fl) → TagsOk tags s → TagsOk tags s₂

section Inv

variable {tags : List TagInst}

theorem tagFields_congr {mi mi' : ModuleInst} {x x' : TagIdx} {ta : Nat}
    (h : mi.tags[x.toNat]? = some ta) (h' : mi'.tags[x'.toNat]? = some ta) :
    tagFields tags mi x = tagFields tags mi' x' := by
  simp only [tagFields, h, h', Option.bind_eq_bind, Option.bind_some]

theorem tag?_inv {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    (ht : s.tag? f x = some (ta, ti)) : f.module.tags[x.toNat]? = some ta ∧ s.tags[ta]? = some ti := by
  simp only [Store.tag?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at ht
  obtain ⟨a, ha, ti', hti, rfl, rfl⟩ := ht
  exact ⟨ha, hti⟩

/-- `throw` keeps the tag invariants. -/
theorem tagsOk_throw {s : Store H} {f : Frame} {x : TagIdx} {ta : Nat} {ti : TagInst}
    {ts : Validation.Ty (.list .val)} {vs : List Val} (hT : TagsOk tags s)
    (ht : s.tag? f x = some (ta, ti)) (he : Validation.Expand ti.type (.func ts .nil))
    (hn : vs.length = ts.length) : TagsOk tags (s.addExn ⟨ta, vs⟩) := by
  obtain ⟨hts, hex⟩ := hT
  refine ⟨hts, fun a e hae mi x' hx' => ?_⟩
  simp only [Store.addExn, List.getElem?_append] at hae
  split at hae
  · exact hex a e hae mi x' hx'
  · rename_i hlt
    rcases Nat.lt_or_ge (a - s.exns.length) 1 with h1 | h1
    · have : a - s.exns.length = 0 := by omega
      simp only [this, List.getElem?_cons_zero, Option.some.injEq] at hae
      subst hae
      have hf := Silmaril.Wasm.Interp.tagFields_of_tag? ht he
      rw [hts] at hf
      rw [tagFields_congr hx' (tag?_inv ht).1, hf, hn]
    · have hnone : ([⟨ta, vs⟩] : List ExnInst)[a - s.exns.length]? = none :=
        List.getElem?_eq_none (by simp only [List.length_singleton]; omega)
      simp [hnone] at hae

/-- A flat instruction keeps the tag invariants. -/
theorem tagsOk_evalFlat {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr}
    {fl : Binaryen.Flow} (h : Binaryen.evalFlat s f stk i = some (s', f', fl)) :
    s'.tags = s.tags ∧ s'.exns = s.exns := by
  cases i <;> simp only [Binaryen.evalFlat] at h
  all_goals (repeat' split at h) <;>
    simp_all [Option.map_eq_some_iff, Option.bind_eq_some_iff, Store.setGlobal, Store.setMem]
  all_goals aesop (add norm simp [Store.setGlobal, Store.setMem])

theorem TagsOk.evalFlat {s s' : Store H} {f f' : Frame} {stk : List Val} {i : Instr}
    {fl : Binaryen.Flow} (hT : TagsOk tags s) (h : Binaryen.evalFlat s f stk i = some (s', f', fl)) :
    TagsOk tags s' := by
  obtain ⟨ht, he⟩ := tagsOk_evalFlat h
  exact ⟨ht ▸ hT.1, fun a e hae => hT.2 a e (he ▸ hae)⟩

end Inv

/-! ## The check of `try_table` -/

section Check

variable {ext : ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
  {labels : List Nat}

theorem chk1_tryTableE {h : Nat} {bt : BlockType} {cs : List Catch} {body : List Binaryen.BExpr}
    {o : Option Nat} (hc : chk1E ext F mi nl ret labels h (.tryTable bt cs body) = some o) :
    ∃ ns np nr, ext F mi (.tryTable bt cs []) = some (.catches ns) ∧
      blockArity mi bt = some (np, nr) ∧ np ≤ h ∧ catchOk labels cs ns = true ∧
      endsAt (chkE ext F mi nl ret (nr :: labels) (some np) body) nr = true ∧
      o = some (h - np + nr) := by
  simp only [chk1E] at hc
  split at hc
  · rename_i ns np nr hx ha
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨ns, np, nr, hx, ha, hcond.1.1, hcond.1.2, hcond.2, (Option.some.inj hc).symm⟩
    · cases hc
  · cases hc

theorem catchOk_cons {c : Catch} {cs : List Catch} {n : Nat} {ns : List Nat}
    (h : catchOk labels (c :: cs) (n :: ns) = true) :
    (∃ m, labels[(catchLabel c).toNat]? = some m ∧ m ≤ n) ∧ catchOk labels cs ns = true := by
  simp only [catchOk, List.length_cons, beq_iff_eq, Nat.add_right_cancel_iff, List.zip_cons_cons,
    List.all_cons, Bool.and_eq_true] at h ⊢
  obtain ⟨hl, hm, hr⟩ := h
  refine ⟨?_, hl, hr⟩
  split at hm
  · rename_i m hm'
    exact ⟨m, hm', by simpa using hm⟩
  · cases hm

end Check

/-- **A caught exception meets its label's arity**: the values the first matching clause pushes
are at least the arity of the label it branches to. -/
theorem catches_count {tags : List TagInst} {s : Store H} {f : Frame} {a : Nat} {labels : List Nat}
    {cs : List Catch} {us : List Val} {l : LabelIdx} {ns : List Nat} (hT : ExnsOk tags s)
    (hc : Cfg.Region.Catches s f a cs (some (us, l)))
    (hns : cs.mapM (clauseCount tags f.module) = some ns) (hok : catchOk labels cs ns = true) :
    ∃ n, labels[l.toNat]? = some n ∧ n ≤ us.length := by
  generalize hr : (some (us, l) : Option (List Val × LabelIdx)) = r at hc
  induction hc generalizing ns with
  | @catch_ x l' cs' e he ht =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
    simp only [List.mapM_cons, clauseCount, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hns
    obtain ⟨n, hn, ns', -, rfl⟩ := hns
    obtain ⟨⟨m, hm, hle⟩, -⟩ := catchOk_cons hok
    rw [hT a e he f.module x ht, Option.some.injEq] at hn
    exact ⟨m, hm, hn ▸ hle⟩
  | @catchRef x l' cs' e he ht =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
    simp only [List.mapM_cons, clauseCount, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hns
    obtain ⟨n, hn, ns', -, rfl⟩ := hns
    obtain ⟨⟨m, hm, hle⟩, -⟩ := catchOk_cons hok
    rw [hT a e he f.module x ht, Option.map_some, Option.some.injEq] at hn
    exact ⟨m, hm, by simp only [List.length_append, List.length_singleton]; omega⟩
  | @catchAll l' cs' =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
    simp only [List.mapM_cons, clauseCount, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hns
    obtain ⟨n, hn, ns', -, rfl⟩ := hns
    obtain ⟨⟨m, hm, hle⟩, -⟩ := catchOk_cons hok
    exact ⟨m, hm, by omega⟩
  | @catchAllRef l' cs' =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
    simp only [List.mapM_cons, clauseCount, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hns
    obtain ⟨n, hn, ns', -, rfl⟩ := hns
    obtain ⟨⟨m, hm, hle⟩, -⟩ := catchOk_cons hok
    exact ⟨m, hm, by simp; omega⟩
  | @next c cs' r' _ _ ih =>
    subst hr
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hns
    obtain ⟨n, -, ns', hns', rfl⟩ := hns
    exact ih hns' (catchOk_cons hok).2 rfl
  | empty => cases hr

/-! ## The arity cases -/

section ArityCases

set_option linter.unusedSectionVars false

variable {tags : List TagInst} {s s₁ s₂ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val}
  {es args body : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow} {fl : Binaryen.Flow}
  {bt : BlockType} {cs : List Catch} {np nr : Nat}

/-- An operator stopping after its arguments, in a store with the same functions, by a trap or a
throw. -/
theorem arityE_opStop {ext : ExtArity H} [ExtStable ext] {i : Instr}
    (iha : ArityGoodE ext s f stk args (s₁, f₁, .normal stk₁) true) (hs : s₂.funcs = s₁.funcs)
    (hfl : fl = .trap ∨ ∃ a, fl = .throw a) :
    ArityGoodE ext s f stk (.op i args :: es) (s₂, f₁, fl) true := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨-, inv1⟩ := arity_args hS iha h1
  refine ⟨?_, hs ▸ inv1.1, inv1.2.1, inv1.2.2⟩
  rcases hfl with rfl | ⟨a, rfl⟩ <;> trivial

/-- What the check of a `try_table` says. -/
theorem arity_try_pre {labels : List Nat} {ret : Nat} {out : Option Nat}
    (har : Binaryen.arity f bt = some (np, nr))
    (hc : chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some stk.length)
      (.tryTable bt cs body :: es) = some out) :
    ∃ ns, cs.mapM (clauseCount tags f.module) = some ns ∧ catchOk labels cs ns = true ∧
      np ≤ stk.length ∧
      endsAt (chkE (ehExt tags) s.funcs f.module f.locals.length ret (nr :: labels) (some np) body)
        nr = true ∧
      chkE (ehExt tags) s.funcs f.module f.locals.length ret labels (some (stk.length - np + nr)) es =
        some out := by
  obtain ⟨o, h1, h2⟩ := chk_consE.mp hc
  obtain ⟨ns, np', nr', hx, ha, hp, hok, hb, ho⟩ := chk1_tryTableE h1
  rw [← arity_eq, har, Option.some.injEq, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  simp only [ehExt, Option.map_eq_some_iff, ExtEff.catches.injEq] at hx
  obtain ⟨ns', hns, rfl⟩ := hx
  exact ⟨ns', hns, hok, hp, hb, ho ▸ h2⟩

theorem arity_tryOk (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, fl) true)
    (hvs : fl.blockVals = some vs)
    (ihk : ArityGoodE (ehExt tags) s₁ f₁ (vs.take nr ++ stk.drop np) es r true) :
    ArityGoodE (ehExt tags) s f stk (.tryTable bt cs body :: es) r true := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, h2⟩ := arity_try_pre har hc
  obtain ⟨ob, hob, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact arity_after hS inv1 hp (blockVals_length hok hob hvs) h2 ihk

theorem arity_tryBrk {k : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, .brk (k + 1) vs) true) :
    ArityGoodE (ehExt tags) s f stk (.tryTable bt cs body :: es) (s₁, f₁, .brk k vs) true := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hc
  obtain ⟨_, _, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact ⟨hok.brk_succ, inv1⟩

theorem arity_tryEsc (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, fl) true) (hfl : fl.Escapes) :
    ArityGoodE (ehExt tags) s f stk (.tryTable bt cs body :: es) (s₁, f₁, fl) true := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hc
  obtain ⟨_, _, hok, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact ⟨hok.escape hfl, inv1⟩

theorem arity_tryCatch {a : Nat} {us : List Val} {l : LabelIdx} (hT : TagsOk tags s₁)
    (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, .throw a) true)
    (hc : Cfg.Region.Catches s₁ f₁ a cs (some (us, l))) :
    ArityGoodE (ehExt tags) s f stk (.tryTable bt cs body :: es)
      (s₁, f₁, .brk l.toNat (us.reverse ++ stk.drop np)) true := by
  intro labels ret out hS hck
  obtain ⟨ns, hns, hok, hp, hb, -⟩ := arity_try_pre har hck
  obtain ⟨_, _, -, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  rw [← inv1.2.1] at hns
  obtain ⟨n, hn, hle⟩ := catches_count hT.2 hc hns hok
  exact ⟨⟨n, hn, by simp only [List.length_append, List.length_reverse]; omega⟩, inv1⟩

theorem arity_tryRethrow {a : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (ihb : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, .throw a) true) :
    ArityGoodE (ehExt tags) s f stk (.tryTable bt cs body :: es) (s₁, f₁, .throw a) true := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hc
  obtain ⟨_, _, -, inv1⟩ := arity_body hS hb (take_length_of_le hp) ihb
  exact ⟨trivial, inv1⟩

end ArityCases

/-! ## The Core cases -/

section CoreCases

set_option linter.unusedSectionVars false

variable {ext : ExtArity H} [ExtStable ext] {eh : Bool} {tags : List TagInst}
  {s s₁ : Store H} {f f₁ : Frame} {stk stk₁ vs : List Val}
  {es args body : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow} {fl : Binaryen.Flow}
  {bt : BlockType} {cs : List Catch} {np nr : Nat}

theorem code_tryTable (stk : List Val) (bt : BlockType) (cs : List Catch)
    (es : List Binaryen.BExpr) :
    vals stk.reverse ++ expression (Binaryen.BExpr.lowerList (.tryTable bt cs body :: es)) =
      vals stk.reverse ++ .plain (.tryTable bt cs (Binaryen.BExpr.lowerList body)) ::
        expression (Binaryen.BExpr.lowerList es) := by
  simp [expression, Binaryen.BExpr.lower]

/-- `throw x`: the exception is allocated with the top fields and thrown (`Step.throw`). -/
theorem core_throw {x : TagIdx} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal stk₁))
    (ht : s₁.tag? f₁ x = some (ta, ti)) (he : Validation.Expand ti.type (.func ts .nil))
    (hn : ts.length ≤ stk₁.length) :
    CoreGoodE ext P host s f stk (.op (.throw x) args :: es)
      (s₁.addExn ⟨ta, (stk₁.take ts.length).reverse⟩, f₁, .throw s₁.exns.length) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  rw [rev_take_drop stk₁ ts.length]
  exact wp_throw ht he (by simp only [List.length_reverse, List.length_take]; omega)
    ⟨rfl, rfl, rfl⟩

/-- `throw_ref` on null traps. -/
theorem core_throwRefNull (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal (.ref .null :: stk₁))) :
    CoreGoodE ext P host s f stk (.op .throwRef args :: es) (s₁, f₁, .trap) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  simpa using wp_throwRef_null (P := P) (host := host) (s := s₁) (f := f₁) (vs := stk₁.reverse)
    (rest := expression (Binaryen.BExpr.lowerList es)) (Q := Match (s₁, f₁, .trap)) ⟨rfl, rfl, trivial⟩

/-- `throw_ref` on an exception reference throws it. -/
theorem core_throwRefExn {a : Nat}
    (iha : CoreGoodE ext P host s f stk args (s₁, f₁, .normal (.ref (.exn a) :: stk₁))) :
    CoreGoodE ext P host s f stk (.op .throwRef args :: es) (s₁, f₁, .throw a) := by
  intro labels ret out hS hc
  obtain ⟨o, h1, -⟩ := chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := chk1_opE h1
  rw [code_op]
  refine wp_append_normal (iha hS ha) ?_
  have e : vals (Val.ref (.exn a) :: stk₁).reverse ++
      .plain .throwRef :: expression (Binaryen.BExpr.lowerList es) =
      vals stk₁.reverse ++ throwing a ++ expression (Binaryen.BExpr.lowerList es) := by
    simp [vals, Val.toAdmin]
  rw [e]
  exact wp_throwing ⟨rfl, rfl, rfl⟩

theorem step_try (har : Binaryen.arity f bt = some (np, nr)) {B : List Instr} (args : List Val)
    (hlen : args.length = np) :
    Step P host ⟨s, f, vals args ++ [.plain (.tryTable bt cs B)]⟩
      ⟨s, f, [.handler nr cs [.label nr [] (vals args ++ expression B)]]⟩ := by
  obtain ⟨t₁, t₂, hbt, h1, h2⟩ := blockType_of_arity har
  subst h2
  exact Step.tryTable hbt (hlen.trans h1.symm)

/-- Entering a `try_table`, below the values it does not consume. -/
theorem steps_try_enter (har : Binaryen.arity f bt = some (np, nr)) {B : List Instr}
    (hp : np ≤ stk.length) (rest : List Admin) :
    Steps P host ⟨s, f, vals stk.reverse ++ .plain (.tryTable bt cs B) :: rest⟩
      ⟨s, f, vals (stk.drop np).reverse ++
        [.handler nr cs [.label nr [] (vals (stk.take np).reverse ++ expression B)]] ++ rest⟩ := by
  have hlen : (stk.take np).reverse.length = np := by
    simp only [List.length_reverse, List.length_take]
    omega
  have e : vals stk.reverse ++ .plain (.tryTable bt cs B) :: rest =
      vals (stk.drop np).reverse ++ (vals (stk.take np).reverse ++ [.plain (.tryTable bt cs B)]) ++
        rest := by
    rw [rev_take_drop stk np]
    simp
  rw [e]
  exact .single (Step.ctx _ rest (step_try har _ hlen))

/-- One step out of a handler for a final form other than a value list or a throw. -/
theorem handler_step_abrupt {n : Nat} {c : List Admin} {o : Outcome} (he : o.Ends c)
    (hm : FlowMatch fl o) (hn : ¬ fl.IsNormal) (hnt : ∀ a, fl ≠ .throw a) :
    ∃ c' o', Step P host ⟨s, f, [.handler n cs c]⟩ ⟨s, f, c'⟩ ∧ o'.Ends c' ∧ FlowMatch fl o' := by
  rcases o with vs | ⟨l, vs⟩ | vs | _ | a | ⟨vs, a, rr⟩ | ⟨vs, rr⟩
  · rcases fl <;> simp_all [FlowMatch, Binaryen.Flow.IsNormal]
  · obtain ⟨x, rest, hx, rfl⟩ := he
    refine ⟨vals vs ++ [.plain (.br x)], .br l vs, ?_, ⟨x, [], hx, by simp⟩, hm⟩
    simpa only [List.append_assoc, List.singleton_append] using
      Step.brHandler (P := P) (host := host) (s := s) (f := f) (n := n) (cs := cs) (vs := vs)
        (l := x) (rest := rest)
  · obtain ⟨rest, rfl⟩ := he
    refine ⟨vals vs ++ [.plain .return_], .ret vs, ?_, ⟨[], by simp⟩, hm⟩
    simpa only [List.append_assoc, List.singleton_append] using
      Step.returnHandler (P := P) (host := host) (s := s) (f := f) (n := n) (cs := cs) (vs := vs)
        (rest := rest)
  · have hc : c = [.trap] := he
    subst hc
    exact ⟨[.trap], .trap, .trapHandler, rfl, hm⟩
  · rcases fl with _ | _ | _ | _ | a' <;> simp only [FlowMatch] at hm
    exact absurd rfl (hnt a')
  · rcases fl <;> simp [FlowMatch] at hm
  · rcases fl <;> simp [FlowMatch] at hm

/-- The run of a `try_table`'s body inside its handler and label, in context. -/
theorem steps_try_body {B c' : List Admin} {pre : List Val} {rest : List Admin} {s' : Store H}
    {f' : Frame} (hrun : Steps P host ⟨s, f, B⟩ ⟨s', f', c'⟩) :
    Steps P host ⟨s, f, vals pre ++ [.handler nr cs [.label nr [] B]] ++ rest⟩
      ⟨s', f', vals pre ++ [.handler nr cs [.label nr [] c']] ++ rest⟩ :=
  Steps.ctx pre rest (Steps.handler (Steps.label nr [] hrun))

/-- **A `try_table` whose body hands on values**: the label and the handler are left. -/
theorem core_tryOk {M : Nat → Store H × Frame × Binaryen.Flow → Post H}
    (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, fl) eh)
    (ihb : CoreGoodE (ehExt tags) P host s f (stk.take np) body (s₁, f₁, fl))
    (hvs : fl.blockVals = some vs)
    (ihk : CoreGoodQ (ehExt tags) P host M s₁ f₁ (vs.take nr ++ stk.drop np) es r) :
    CoreGoodQ (ehExt tags) P host M s f stk (.tryTable bt cs body :: es) r := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, h2⟩ := arity_try_pre har hc
  obtain ⟨ob, hob, hbc, hok, inv1⟩ := body_facts hS hbody hb (take_length_of_le hp)
  have hnr : nr ≤ vs.length := blockVals_length hok hob hvs
  have hnorm : ∀ ws, fl = .normal ws → ws.length = nr := by
    rintro ws rfl
    exact length_of_ends hok hob
  have hk := ihk (storeChk_inv inv1 hS) (chk_after inv1 hp hnr h2)
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (ihb hS hbc)
  rw [code_tryTable]
  have enter := steps_try_enter (P := P) (host := host) (s := s) (cs := cs)
    (B := Binaryen.BExpr.lowerList body) har hp (expression (Binaryen.BExpr.lowerList es))
  have hx : Steps P host ⟨s₁, f₁, [.label nr [] c']⟩ ⟨s₁, f₁, vals (vs.take nr).reverse⟩ := by
    simpa using exit_blockVals (P := P) (host := host) (pre := []) (rest := []) he hm hvs hnr hnorm
  have hout : Steps P host ⟨s₁, f₁, [.handler nr cs [.label nr [] c']]⟩
      ⟨s₁, f₁, vals (vs.take nr).reverse⟩ :=
    (Steps.handler hx).tail Step.handlerVals
  have inner := Steps.ctx (P := P) (host := host) (stk.drop np).reverse
    (expression (Binaryen.BExpr.lowerList es)) hout
  have hk' : WP P host s₁ f₁ (vals (stk.drop np).reverse ++ vals (vs.take nr).reverse ++
      expression (Binaryen.BExpr.lowerList es)) (M ret r) := by
    rw [← vals_append, ← stack_after]
    exact hk
  exact WP.steps (enter.trans ((steps_try_body hrun).trans inner)) hk'

/-- **A `try_table` whose body branches past it, returns or traps**: the flow leaves the label
and passes through the handler. -/
theorem core_tryAbrupt {fl' : Binaryen.Flow} (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, fl) eh)
    (ihb : CoreGoodE (ehExt tags) P host s f (stk.take np) body (s₁, f₁, fl))
    (hfl : (∃ k vs, fl = .brk (k + 1) vs ∧ fl' = .brk k vs) ∨ (fl.Escapes ∧ fl' = fl))
    (hnt : ∀ a, fl ≠ .throw a) :
    CoreGoodE (ehExt tags) P host s f stk (.tryTable bt cs body :: es) (s₁, f₁, fl') := by
  intro labels ret out hS hc
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hc
  obtain ⟨_, _, hbc, -⟩ := body_facts hS hbody hb (take_length_of_le hp)
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (ihb hS hbc)
  have hn' : ¬ fl'.IsNormal := by
    rcases hfl with ⟨k, vs, rfl, rfl⟩ | ⟨hesc, hfeq⟩
    · exact id
    · rw [hfeq]
      cases fl <;> simp_all [Binaryen.Flow.Escapes, Binaryen.Flow.IsNormal]
  have hnt' : ∀ a, fl' ≠ .throw a := by
    rcases hfl with ⟨k, vs, rfl, rfl⟩ | ⟨-, hfeq⟩
    · intro a h; cases h
    · exact hfeq ▸ hnt
  obtain ⟨c₁, o₁, hst₁, he₁, hm₁⟩ := label_step_abrupt (P := P) (host := host) (s₁ := s₁) (f₁ := f₁)
    (n := nr) (cont := []) he hm hfl
  obtain ⟨c₂, o₂, hst₂, he₂, hm₂⟩ := handler_step_abrupt (P := P) (host := host) (s := s₁)
    (f := f₁) (n := nr) (cs := cs) he₁ hm₁ hn' hnt'
  have hout : Steps P host ⟨s₁, f₁, [.handler nr cs [.label nr [] c']]⟩ ⟨s₁, f₁, c₂⟩ :=
    (Steps.handler (Relation.ReflTransGen.single hst₁)).tail hst₂
  rw [code_tryTable]
  have enter := steps_try_enter (P := P) (host := host) (s := s) (cs := cs)
    (B := Binaryen.BExpr.lowerList body) har hp (expression (Binaryen.BExpr.lowerList es))
  exact WP.steps (enter.trans ((steps_try_body hrun).trans
    (Steps.ctx (stk.drop np).reverse _ hout))) (wp_abrupt he₂ hm₂ hn' _ _)

/-- **A caught exception** (`Cfg.Region.Catches`, first match): the throw leaves the label, and
the handler branches to the clause's label with its values, from outside the `try_table`. -/
theorem core_tryCatch {a : Nat} {us : List Val} {l : LabelIdx}
    (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, .throw a) eh)
    (ihb : CoreGoodE (ehExt tags) P host s f (stk.take np) body (s₁, f₁, .throw a))
    (hc : Cfg.Region.Catches s₁ f₁ a cs (some (us, l))) :
    CoreGoodE (ehExt tags) P host s f stk (.tryTable bt cs body :: es)
      (s₁, f₁, .brk l.toNat (us.reverse ++ stk.drop np)) := by
  intro labels ret out hS hck
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hck
  obtain ⟨_, _, hbc, -⟩ := body_facts hS hbody hb (take_length_of_le hp)
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (ihb hS hbc)
  have hc' : c' = throwing a := by
    rcases o with _ | _ | _ | _ | a' | _ | _ <;> simp only [FlowMatch] at hm
    subst hm
    exact he
  subst hc'
  have hout : Steps P host ⟨s₁, f₁, [.handler nr cs [.label nr [] (throwing a)]]⟩
      ⟨s₁, f₁, vals us ++ [.plain (.br l)]⟩ :=
    (Steps.handler (Relation.ReflTransGen.single Step.throwRefLabel)).trans
      (Cfg.Region.catches_steps hc)
  rw [code_tryTable]
  have enter := steps_try_enter (P := P) (host := host) (s := s) (cs := cs)
    (B := Binaryen.BExpr.lowerList body) har hp (expression (Binaryen.BExpr.lowerList es))
  refine WP.steps (enter.trans ((steps_try_body hrun).trans
    (Steps.ctx (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es)) hout)))
    ⟨s₁, f₁, _, .br l.toNat ((stk.drop np).reverse ++ us), .refl,
      ⟨l, expression (Binaryen.BExpr.lowerList es), rfl, by simp⟩, rfl, rfl, rfl, [], by simp⟩

/-- **No clause matches**: the handler rethrows the exception. -/
theorem core_tryRethrow {a : Nat} (har : Binaryen.arity f bt = some (np, nr))
    (hbody : ArityGoodE (ehExt tags) s f (stk.take np) body (s₁, f₁, .throw a) eh)
    (ihb : CoreGoodE (ehExt tags) P host s f (stk.take np) body (s₁, f₁, .throw a))
    (hc : Cfg.Region.Catches s₁ f₁ a cs none) :
    CoreGoodE (ehExt tags) P host s f stk (.tryTable bt cs body :: es) (s₁, f₁, .throw a) := by
  intro labels ret out hS hck
  obtain ⟨-, -, -, hp, hb, -⟩ := arity_try_pre har hck
  obtain ⟨_, _, hbc, -⟩ := body_facts hS hbody hb (take_length_of_le hp)
  obtain ⟨c', o, hrun, he, hm⟩ := run_of_wp (ihb hS hbc)
  have hc' : c' = throwing a := by
    rcases o with _ | _ | _ | _ | a' | _ | _ <;> simp only [FlowMatch] at hm
    subst hm
    exact he
  subst hc'
  have hout : Steps P host ⟨s₁, f₁, [.handler nr cs [.label nr [] (throwing a)]]⟩
      ⟨s₁, f₁, throwing a⟩ :=
    (Steps.handler (Relation.ReflTransGen.single Step.throwRefLabel)).trans
      (Cfg.Region.catches_steps_none hc)
  rw [code_tryTable]
  have enter := steps_try_enter (P := P) (host := host) (s := s) (cs := cs)
    (B := Binaryen.BExpr.lowerList body) har hp (expression (Binaryen.BExpr.lowerList es))
  exact WP.steps (enter.trans ((steps_try_body hrun).trans
    (Steps.ctx (stk.drop np).reverse (expression (Binaryen.BExpr.lowerList es)) hout)))
    (wp_throwing ⟨rfl, rfl, rfl⟩)

end CoreCases

/-! ## The simulation -/

section Free

theorem xFreeL_op {i : Instr} {args es : List Binaryen.BExpr} (h : xFreeL (.op i args :: es) = true) :
    isXCall i = false ∧ xFreeL args = true ∧ xFreeL es = true := by
  simp_all [xFreeL, xFree]

theorem xFreeL_block {bt : BlockType} {body es : List Binaryen.BExpr}
    (h : xFreeL (.block bt body :: es) = true) : xFreeL body = true ∧ xFreeL es = true := by
  simp_all [xFreeL, xFree]

theorem xFreeL_loop {bt : BlockType} {body es : List Binaryen.BExpr}
    (h : xFreeL (.loop bt body :: es) = true) : xFreeL body = true ∧ xFreeL es = true := by
  simp_all [xFreeL, xFree]

theorem xFreeL_tryTable {bt : BlockType} {cs : List Catch} {body es : List Binaryen.BExpr}
    (h : xFreeL (.tryTable bt cs body :: es) = true) : xFreeL body = true ∧ xFreeL es = true := by
  simp_all [xFreeL, xFree]

theorem xFreeL_if {bt : BlockType} {c t el es : List Binaryen.BExpr} (b : Bool)
    (h : xFreeL (.if_ bt c t el :: es) = true) :
    xFreeL c = true ∧ xFreeL (if b then t else el) = true ∧ xFreeL es = true := by
  cases b <;> simp_all [xFreeL, xFree]

theorem tailRes_isXCall {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {o : Option (Nat × List Val)} (h : TailRes s f i stk o) : isXCall i = true := by
  cases h <;> rfl

end Free

/-- **Forward simulation with exceptions**: with the exception checker `ehExt tags` and
exceptions on, every `EvalOXE C` run of checked code without the extended call forms is a
Core 3.0 run, with the arity invariants and the tag invariants. `throw`, `throw_ref` and
`try_table` (with the first-match resolution `Cfg.Region.Catches`) run as Core's exception
rules, and the oracle's callees may throw. -/
theorem evalOXE_goodEH {tags : List TagInst} {C : Abstract.CallRel H}
    (hC : OracleSoundE (ehExt tags) P host C true) (hT : OracleThrowsE (ehExt tags) P host C)
    (hG : OracleTagsE tags C) {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} {r : Store H × Frame × Binaryen.Flow}
    (h : EvalOXE C s f stk es r) :
    xFreeL es = true → TagsOk tags s →
      TagsOk tags r.1 ∧ ArityGoodE (ehExt tags) s f stk es r true ∧
        CoreGoodE (ehExt tags) P host s f stk es r := by
  induction h with
  | nil => exact fun _ hts => ⟨hts, arity_nil, core_nil⟩
  | argsAbort _ hfl iha =>
    intro hx hts
    obtain ⟨ta, aa, ca⟩ := iha (xFreeL_op hx).2.1 hts
    exact ⟨ta, arity_argsAbort aa hfl, core_argsAbort ca hfl⟩
  | callOk _ hfi hty hcall hvs _ iha ihk =>
    intro hx hts
    obtain ⟨-, hxa, hxe⟩ := xFreeL_op hx
    obtain ⟨ta, aa, ca⟩ := iha hxa hts
    obtain ⟨tk, ak, ck⟩ := ihk hxe (hG _ _ _ _ _ hcall ta)
    exact ⟨tk, arityO_callOk hC aa hfi hty hcall hvs ak,
      coreO_callOk hC aa ca hfi hty hcall hvs ck⟩
  | callTrap _ hfi hty hcall iha =>
    intro hx hts
    obtain ⟨ta, aa, ca⟩ := iha (xFreeL_op hx).2.1 hts
    exact ⟨hG _ _ _ _ _ hcall ta, arityO_callTrap hC aa hfi hty hcall,
      coreO_callTrap hC aa ca hfi hty hcall⟩
  | callThrow _ hfi hty hcall iha =>
    intro hx hts
    obtain ⟨ta, aa, ca⟩ := iha (xFreeL_op hx).2.1 hts
    exact ⟨hG _ _ _ _ _ hcall ta, arityO_callThrow hC aa hfi hty hcall,
      coreO_callThrowE hT aa ca hfi hty hcall⟩
  | opOk hi _ hflat _ iha ihk =>
    intro hx hts
    obtain ⟨-, hxa, hxe⟩ := xFreeL_op hx
    obtain ⟨ta, aa, ca⟩ := iha hxa hts
    obtain ⟨tk, ak, ck⟩ := ihk hxe (ta.evalFlat hflat)
    exact ⟨tk, arity_opOk aa hflat ak, core_opOk aa ca hi hflat ck⟩
  | opStop _ _ hflat hfl iha =>
    intro hx hts
    obtain ⟨ta, aa, ca⟩ := iha (xFreeL_op hx).2.1 hts
    exact ⟨ta.evalFlat hflat, arity_opStop aa hflat hfl, core_opStop aa ca hflat hfl⟩
  | blockOk har _ hvs _ ihb ihk =>
    intro hx hts
    obtain ⟨hxb, hxe⟩ := xFreeL_block hx
    obtain ⟨tb, ab, cb⟩ := ihb hxb hts
    obtain ⟨tk, ak, ck⟩ := ihk hxe tb
    exact ⟨tk, arity_blockOk har ab hvs ak, core_blockOk har ab cb hvs ck⟩
  | blockBrk har _ ihb =>
    intro hx hts
    obtain ⟨tb, ab, cb⟩ := ihb (xFreeL_block hx).1 hts
    exact ⟨tb, arity_blockBrk har ab, core_blockAbrupt har ab cb (.inl ⟨_, _, rfl, rfl⟩)⟩
  | blockEsc har _ hfl ihb =>
    intro hx hts
    obtain ⟨tb, ab, cb⟩ := ihb (xFreeL_block hx).1 hts
    exact ⟨tb, arity_blockEsc har ab hfl, core_blockAbrupt har ab cb (.inr ⟨hfl, rfl⟩)⟩
  | loopOk har _ _ ihb ihk =>
    intro hx hts
    obtain ⟨hxb, hxe⟩ := xFreeL_loop hx
    obtain ⟨tb, ab, cb⟩ := ihb hxb hts
    obtain ⟨tk, ak, ck⟩ := ihk hxe tb
    exact ⟨tk, arity_loopOk har ab ak, core_loopOk har ab cb ck⟩
  | loopBack har _ _ ihb ihk =>
    intro hx hts
    obtain ⟨tb, ab, cb⟩ := ihb (xFreeL_loop hx).1 hts
    obtain ⟨tk, ak, ck⟩ := ihk hx tb
    exact ⟨tk, arity_loopBack har ab ak, core_loopBack har ab cb ck⟩
  | loopBrk har _ ihb =>
    intro hx hts
    obtain ⟨tb, ab, cb⟩ := ihb (xFreeL_loop hx).1 hts
    exact ⟨tb, arity_loopBrk har ab, core_loopAbrupt har ab cb (.inl ⟨_, _, rfl, rfl⟩)⟩
  | loopEsc har _ hfl ihb =>
    intro hx hts
    obtain ⟨tb, ab, cb⟩ := ihb (xFreeL_loop hx).1 hts
    exact ⟨tb, arity_loopEsc har ab hfl, core_loopAbrupt har ab cb (.inr ⟨hfl, rfl⟩)⟩
  | @ifOk _ _ _ _ _ _ _ _ _ cv b _ _ _ _ _ _ _ _ _ _ hb har _ hvs _ ihc iharm ihk =>
    intro hx hts
    obtain ⟨hxc, hxm, hxe⟩ := xFreeL_if b hx
    obtain ⟨tc, ac, cc⟩ := ihc hxc hts
    obtain ⟨tm, am, cm⟩ := iharm hxm tc
    obtain ⟨tk, ak, ck⟩ := ihk hxe tm
    exact ⟨tk, arity_ifOk ac har am hvs ak, core_ifOk ac cc hb har am cm hvs ck⟩
  | @ifBrk _ _ _ _ _ _ _ _ _ cv b _ _ _ _ _ _ _ _ _ hb har _ ihc iharm =>
    intro hx hts
    obtain ⟨hxc, hxm, -⟩ := xFreeL_if b hx
    obtain ⟨tc, ac, cc⟩ := ihc hxc hts
    obtain ⟨tm, am, cm⟩ := iharm hxm tc
    exact ⟨tm, arity_ifBrk ac har am,
      core_ifAbrupt ac cc hb har am cm (.inl ⟨_, _, rfl, rfl⟩)⟩
  | @ifEsc _ _ _ _ _ _ _ _ cv b _ _ _ _ _ _ _ _ _ hb har _ hfl ihc iharm =>
    intro hx hts
    obtain ⟨hxc, hxm, -⟩ := xFreeL_if b hx
    obtain ⟨tc, ac, cc⟩ := ihc hxc hts
    obtain ⟨tm, am, cm⟩ := iharm hxm tc
    exact ⟨tm, arity_ifEsc ac har am hfl, core_ifAbrupt ac cc hb har am cm (.inr ⟨hfl, rfl⟩)⟩
  | ifAbort _ hfl ihc =>
    intro hx hts
    obtain ⟨tc, ac, cc⟩ := ihc (xFreeL_if true hx).1 hts
    exact ⟨tc, arity_ifAbort ac hfl, core_ifAbort cc hfl⟩
  | callIndOk => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndRes => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callIndStop => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefOk => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefNull => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | callRefStop => intro hx; simp [xFreeL, xFree, isXCall] at hx
  | tail _ hres =>
    intro hx
    have := (xFreeL_op hx).1
    rw [tailRes_isXCall hres] at this
    cases this
  | tailRes _ hres =>
    intro hx
    have := (xFreeL_op hx).1
    rw [tailRes_isXCall hres] at this
    cases this
  | throw _ ht he hn iha =>
    intro hx hts
    obtain ⟨ta, aa, ca⟩ := iha (xFreeL_op hx).2.1 hts
    exact ⟨tagsOk_throw ta ht he (by simp only [List.length_reverse, List.length_take]; omega),
      arityE_opStop aa rfl (.inr ⟨_, rfl⟩), core_throw ca ht he hn⟩
  | throwRefNull _ iha =>
    intro hx hts
    obtain ⟨ta, aa, ca⟩ := iha (xFreeL_op hx).2.1 hts
    exact ⟨ta, arityE_opStop aa rfl (.inl rfl), core_throwRefNull ca⟩
  | throwRefExn _ iha =>
    intro hx hts
    obtain ⟨ta, aa, ca⟩ := iha (xFreeL_op hx).2.1 hts
    exact ⟨ta, arityE_opStop aa rfl (.inr ⟨_, rfl⟩), core_throwRefExn ca⟩
  | tryOk har _ hvs _ ihb ihk =>
    intro hx hts
    obtain ⟨hxb, hxe⟩ := xFreeL_tryTable hx
    obtain ⟨tb, ab, cb⟩ := ihb hxb hts
    obtain ⟨tk, ak, ck⟩ := ihk hxe tb
    exact ⟨tk, arity_tryOk har ab hvs ak, core_tryOk har ab cb hvs ck⟩
  | tryBrk har _ ihb =>
    intro hx hts
    obtain ⟨tb, ab, cb⟩ := ihb (xFreeL_tryTable hx).1 hts
    exact ⟨tb, arity_tryBrk har ab,
      core_tryAbrupt har ab cb (.inl ⟨_, _, rfl, rfl⟩) (fun _ h => by cases h)⟩
  | tryEsc har _ hfl hnt ihb =>
    intro hx hts
    obtain ⟨tb, ab, cb⟩ := ihb (xFreeL_tryTable hx).1 hts
    exact ⟨tb, arity_tryEsc har ab hfl, core_tryAbrupt har ab cb (.inr ⟨hfl, rfl⟩) hnt⟩
  | tryCatch har _ hc ihb =>
    intro hx hts
    obtain ⟨tb, ab, cb⟩ := ihb (xFreeL_tryTable hx).1 hts
    exact ⟨tb, arity_tryCatch tb har ab hc, core_tryCatch har ab cb hc⟩
  | tryRethrow har _ hc ihb =>
    intro hx hts
    obtain ⟨tb, ab, cb⟩ := ihb (xFreeL_tryTable hx).1 hts
    exact ⟨tb, arity_tryRethrow har ab, core_tryRethrow har ab cb hc⟩

end Silmaril.Wasm.Interp
