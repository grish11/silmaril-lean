module

public import Silmaril.Proofs.Wasm.Abstract.FragBody.Typed

/-!
# The typed fragment: progress

Typed code on typed locals either has a big-step outcome or diverges through
a loop (`DivE`): it is never stuck. The loop case builds the infinite chain
of `br 0` iterations by choice, using preservation to keep the locals typed.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FragBody

open Silmaril.Wasm.Abstract.FragBody Silmaril.Wasm.SSA

variable {Γ : List Silmaril.Wasm.IntType} {ρ : Option Silmaril.Wasm.IntType}

theorem args_ty {Λ : List (Option Silmaril.Wasm.IntType)} :
    ∀ {es : List Expr} {ls : List WVal} {o : Out (List WVal)} {ts : List Silmaril.Wasm.IntType},
      Args ls es o → ArgsTy Γ ρ Λ es ts → ValsTy Γ ls → OutTy Γ ρ Λ (ValsTy ts) o
  | [], ls, o, ts, h, hty, hls => by cases h; cases hty; exact .ok hls rfl
  | e :: es, ls, o, ts, h, hty, hls => by
    cases hty with
    | cons he hes =>
      cases h with
      | cons h₁ h₂ =>
        cases exec_ty h₁ he hls with
        | ok hls₁ hv =>
          cases args_ty h₂ hes hls₁ with
          | ok hls₂ hvs => exact .ok hls₂ (by simp_all [ValsTy, ValTy])
      | head_abrupt h₁ hab => exact OutTy.abrupt (exec_ty h₁ he hls) hab
      | tail_abrupt h₁ h₂ hab =>
        cases exec_ty h₁ he hls with
        | ok hls₁ _ => exact OutTy.abrupt' (args_ty h₂ hes hls₁) hab

theorem truthy_of_i32 {v : WVal} (h : v.type = .i32) : ∃ b, v.truthy = some b := by
  cases v with
  | i32 x => exact ⟨_, rfl⟩
  | i64 x => cases h

theorem asInt_of_type {v : WVal} {t : Silmaril.Wasm.IntType} (h : v.type = t) :
    ∃ x, v.asInt t = some x := by
  subst h; cases v <;> exact ⟨_, rfl⟩

set_option linter.unusedSimpArgs false in
theorem opSig_progress {o : Op} {ts : List Silmaril.Wasm.IntType} {t : Silmaril.Wasm.IntType}
    {vs : List WVal} (hs : OpSig o ts t) (hv : ValsTy ts vs) :
    (∃ v, o.eval vs = some (.val v)) ∨ o.eval vs = some .trap := by
  cases hs with
  | const v => cases vs <;> simp_all [ValsTy, Op.eval]
  | unInt t op =>
    rcases vs with _ | ⟨a, _ | _⟩ <;> simp only [ValsTy, List.map, List.cons.injEq,
      List.map_eq_nil_iff, reduceCtorEq, and_false, false_and] at hv
    obtain ⟨x, hx⟩ := asInt_of_type hv.1
    exact .inl ⟨.ofInt t (Silmaril.Wasm.Numerics.intUnOp t op x), by simp [Op.eval, UnOp.eval, hx]⟩
  | test t =>
    rcases vs with _ | ⟨a, _ | _⟩ <;> simp only [ValsTy, List.map, List.cons.injEq,
      List.map_eq_nil_iff, reduceCtorEq, and_false, false_and] at hv
    obtain ⟨x, hx⟩ := asInt_of_type hv.1
    exact .inl ⟨.i32 (Silmaril.Wasm.Numerics.intTestOp t .eqz x), by simp [Op.eval, UnOp.eval, hx]⟩
  | binInt t op =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp only [ValsTy, List.map, List.cons.injEq,
      List.map_eq_nil_iff, reduceCtorEq, and_false, false_and] at hv
    obtain ⟨x, hx⟩ := asInt_of_type hv.1
    obtain ⟨y, hy⟩ := asInt_of_type hv.2.1
    cases hz : Silmaril.Wasm.Numerics.intBinOp t op x y with
    | ok z => exact .inl ⟨.ofInt t z, by simp [Op.eval, BinOp.eval, hx, hy, hz]⟩
    | error _ => exact .inr (by simp [Op.eval, BinOp.eval, hx, hy, hz])
  | rel t op =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp only [ValsTy, List.map, List.cons.injEq,
      List.map_eq_nil_iff, reduceCtorEq, and_false, false_and] at hv
    obtain ⟨x, hx⟩ := asInt_of_type hv.1
    obtain ⟨y, hy⟩ := asInt_of_type hv.2.1
    exact .inl ⟨.i32 (Silmaril.Wasm.Numerics.intRelOp t op x y), by simp [Op.eval, BinOp.eval, hx, hy]⟩
  | select t =>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> simp only [ValsTy, List.map,
      List.cons.injEq, List.map_eq_nil_iff, reduceCtorEq, and_false, false_and] at hv
    obtain ⟨bb, hb⟩ := truthy_of_i32 hv.2.2.1
    exact .inl ⟨if bb then a else b, by simp [Op.eval, hb]⟩

theorem get_of_ty {ls : List WVal} {i : Nat} {t : Silmaril.Wasm.IntType} (hl : ValsTy Γ ls)
    (hg : Γ[i]? = some t) : ∃ v, ls[i]? = some v := by
  have := congrArg (·[i]?) hl
  simp only [List.getElem?_map, hg] at this
  rcases h : ls[i]? with _ | v
  · rw [h] at this; cases this
  · exact ⟨v, rfl⟩

theorem blockOk_of {ty : Option Silmaril.Wasm.IntType} {r : Option WVal} (h : ValTy ty r) :
    BlockOk ty r := by
  cases ty <;> cases r <;> simp_all [BlockOk, ValTy]

theorem blockExit_exists {Λ : List (Option Silmaril.Wasm.IntType)}
    {ty : Option Silmaril.Wasm.IntType} {o : Out (Option WVal)}
    (h : OutTy Γ ρ (ty :: Λ) (ValTy ty) o) : ∃ o', BlockExit ty o o' := by
  cases h with
  | ok _ hv => exact ⟨_, .ok (blockOk_of hv)⟩
  | @brk l _ _ _ hl _ hv =>
    cases l with
    | zero => simp at hl; subst hl; exact ⟨_, .brk0 (blockOk_of hv)⟩
    | succ l => exact ⟨_, .brk⟩
  | ret => exact ⟨_, .ret⟩
  | trap => exact ⟨_, .trap⟩

theorem loopExit_exists {Λ : List (Option Silmaril.Wasm.IntType)}
    {ty : Option Silmaril.Wasm.IntType} {o : Out (Option WVal)}
    (h : OutTy Γ ρ (none :: Λ) (ValTy ty) o) :
    (∃ ls r, o = .brk 0 ls r ∧ ValsTy Γ ls) ∨ ∃ o', LoopExit ty o o' := by
  cases h with
  | ok _ hv => exact .inr ⟨_, .ok (blockOk_of hv)⟩
  | @brk l _ _ _ hl hls _ =>
    cases l with
    | zero => exact .inl ⟨_, _, rfl, hls⟩
    | succ l => exact .inr ⟨_, .brk⟩
  | ret => exact .inr ⟨_, .ret⟩
  | trap => exact .inr ⟨_, .trap⟩

theorem getLast_of_ty {lt : Option Silmaril.Wasm.IntType} {vs : List WVal}
    (h : ValsTy (lt.toList ++ [.i32]) vs) : ∃ c, vs.getLast? = some c ∧ c.type = .i32 := by
  cases lt <;> rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> simp_all [ValsTy]


theorem loop_progress {Λ : List (Option Silmaril.Wasm.IntType)} {ty : Option Silmaril.Wasm.IntType}
    {body : List Expr} (hb : SeqTy Γ ρ (none :: Λ) body ty)
    (ih : ∀ ls, ValsTy Γ ls → (∃ o, Seq ls none body o) ∨ DivS ls none body)
    {ls : List WVal} (hls : ValsTy Γ ls) :
    (∃ o, Exec ls (.loop ty body) o) ∨ DivE ls (.loop ty body) := by
  by_contra hbad
  let Bad : List WVal → Prop := fun ls =>
    ValsTy Γ ls ∧ ¬ ((∃ o, Exec ls (.loop ty body) o) ∨ DivE ls (.loop ty body))
  have step : ∀ ls, Bad ls → ∃ p : List WVal × Option WVal,
      Seq ls none body (.brk 0 p.1 p.2) ∧ Bad p.1 := by
    intro ls ⟨hls, hno⟩
    rcases ih ls hls with ⟨out, hs⟩ | hd
    · have hty := seq_ty hs hb hls (fun h => by subst h; cases hb; rfl)
      rcases loopExit_exists hty with ⟨ls', r, rfl, hls'⟩ | ⟨o', hx⟩
      · refine ⟨(ls', r), hs, hls', fun h => hno ?_⟩
        rcases h with ⟨o, he⟩ | hd
        · exact .inl ⟨o, .loop_back hs he⟩
        · exact .inr (.loopBack hs hd)
      · exact absurd (.inl ⟨o', .loop hs hx⟩) hno
    · exact absurd (.inr (.loopBody hd)) hno
  let T := {ls // Bad ls}
  let g : T → T := fun x => ⟨(Classical.choose (step x.1 x.2)).1,
    (Classical.choose_spec (step x.1 x.2)).2⟩
  let x₀ : T := ⟨ls, hls, hbad⟩
  refine hbad (.inr (.loopInf (fun n => (g^[n] x₀).1)
    (fun n => (Classical.choose (step (g^[n] x₀).1 (g^[n] x₀).2)).2) rfl fun n => ?_))
  rw [Function.iterate_succ_apply']
  exact (Classical.choose_spec (step (g^[n] x₀).1 (g^[n] x₀).2)).1

mutual

theorem prog_e : (e : Expr) → ∀ {Λ r ls}, Ty Γ ρ Λ e r → ValsTy Γ ls →
    (∃ o, Exec ls e o) ∨ DivE ls e
  | .op o args, Λ, r, ls, hty, hls => by
    cases hty with
    | op hs ha =>
      rcases prog_a args ha hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls' vs =>
          cases args_ty h ha hls with
          | ok _ hvs =>
            rcases opSig_progress hs hvs with ⟨v, hv⟩ | hv
            · exact .inl ⟨_, .op h hv⟩
            · exact .inl ⟨_, .op_trap h hv⟩
        | _ => exact .inl ⟨_, .op_abrupt h trivial⟩
      · exact .inr (.op hd)
  | .localGet i, Λ, r, ls, hty, hls => by
    cases hty with
    | localGet hg => obtain ⟨v, hv⟩ := get_of_ty hls hg; exact .inl ⟨_, .localGet hv⟩
  | .localSet i e, Λ, r, ls, hty, hls => by
    cases hty with
    | localSet hg he =>
      rcases prog_e e he hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls' v =>
          cases exec_ty h he hls with
          | ok _ hv =>
            cases v with
            | none => simp [ValTy] at hv
            | some v => exact .inl ⟨_, .localSet h⟩
        | _ => exact .inl ⟨_, .localSet_abrupt h trivial⟩
      · exact .inr (.localSet hd)
  | .localTee i e, Λ, r, ls, hty, hls => by
    cases hty with
    | localTee hg he =>
      rcases prog_e e he hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls' v =>
          cases exec_ty h he hls with
          | ok _ hv =>
            cases v with
            | none => simp [ValTy] at hv
            | some v => exact .inl ⟨_, .localTee h⟩
        | _ => exact .inl ⟨_, .localTee_abrupt h trivial⟩
      · exact .inr (.localTee hd)
  | .drop e, Λ, r, ls, hty, hls => by
    cases hty with
    | drop he =>
      rcases prog_e e he hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls' v => exact .inl ⟨_, .drop h⟩
        | _ => exact .inl ⟨_, .drop_abrupt h trivial⟩
      · exact .inr (.drop hd)
  | .nop, Λ, r, ls, hty, hls => .inl ⟨_, .nop⟩
  | .unreachable, Λ, r, ls, hty, hls => .inl ⟨_, .unreachable⟩
  | .block ty body, Λ, r, ls, hty, hls => by
    cases hty with
    | block hb =>
      rcases prog_s body hb hls (r0 := none) with ⟨out, h⟩ | hd
      · obtain ⟨o', hx⟩ := blockExit_exists (seq_ty h hb hls (fun h => by subst h; cases hb; rfl))
        exact .inl ⟨_, .block h hx⟩
      · exact .inr (.block hd)
  | .loop ty body, Λ, r, ls, hty, hls => by
    cases hty with
    | loop hb => exact loop_progress hb (fun ls hls => prog_s body hb hls (r0 := none)) hls
  | .if_ ty c t e, Λ, r, ls, hty, hls => by
    cases hty with
    | if_ hc ht he =>
      rcases prog_e c hc hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls₁ v =>
          cases exec_ty h hc hls with
          | ok hls₁ hv =>
            cases v with
            | none => simp [ValTy] at hv
            | some cv =>
              obtain ⟨b, hb⟩ := truthy_of_i32 (by simpa [ValTy] using hv)
              cases b
              · rcases prog_s e he hls₁ (r0 := none) with ⟨out', h'⟩ | hd
                · obtain ⟨o', hx⟩ :=
                    blockExit_exists (seq_ty h' he hls₁ (fun h => by subst h; cases he; rfl))
                  exact .inl ⟨_, .if_ h hb (by simpa using h') hx⟩
                · exact .inr (.ifElse h hb hd)
              · rcases prog_s t ht hls₁ (r0 := none) with ⟨out', h'⟩ | hd
                · obtain ⟨o', hx⟩ :=
                    blockExit_exists (seq_ty h' ht hls₁ (fun h => by subst h; cases ht; rfl))
                  exact .inl ⟨_, .if_ h hb (by simpa using h') hx⟩
                · exact .inr (.ifThen h hb hd)
        | _ => exact .inl ⟨_, .if_abrupt h trivial⟩
      · exact .inr (.ifCond hd)
  | .br l args, Λ, r, ls, hty, hls => by
    cases hty with
    | br hl ha =>
      rcases prog_a args ha hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls' vs => exact .inl ⟨_, .br h⟩
        | _ => exact .inl ⟨_, .br_abrupt h trivial⟩
      · exact .inr (.br hd)
  | .brIf l args, Λ, r, ls, hty, hls => by
    cases hty with
    | brIf hl ha =>
      rcases prog_a args ha hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls' vs =>
          cases args_ty h ha hls with
          | ok _ hvs =>
            obtain ⟨c, hc, hct⟩ := getLast_of_ty hvs
            obtain ⟨b, hb⟩ := truthy_of_i32 hct
            exact .inl ⟨_, .brIf h hc hb⟩
        | _ => exact .inl ⟨_, .brIf_abrupt h trivial⟩
      · exact .inr (.brIf hd)
  | .return_ args, Λ, r, ls, hty, hls => by
    cases hty with
    | return_ ha =>
      rcases prog_a args ha hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls' vs => exact .inl ⟨_, .return_ h⟩
        | _ => exact .inl ⟨_, .return_abrupt h trivial⟩
      · exact .inr (.return_ hd)

theorem prog_a : (es : List Expr) → ∀ {Λ ts ls}, ArgsTy Γ ρ Λ es ts → ValsTy Γ ls →
    (∃ o, Args ls es o) ∨ DivA ls es
  | [], Λ, ts, ls, hty, hls => .inl ⟨_, .nil⟩
  | e :: es, Λ, ts, ls, hty, hls => by
    cases hty with
    | cons he hes =>
      rcases prog_e e he hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls₁ v =>
          cases exec_ty h he hls with
          | ok hls₁ hv =>
            cases v with
            | none => simp [ValTy] at hv
            | some v =>
              rcases prog_a es hes hls₁ with ⟨out', h'⟩ | hd
              · cases out' with
                | ok ls₂ vs => exact .inl ⟨_, .cons h h'⟩
                | _ => exact .inl ⟨_, .tail_abrupt h h' trivial⟩
              · exact .inr (.tail h hd)
        | _ => exact .inl ⟨_, .head_abrupt h trivial⟩
      · exact .inr (.head hd)

theorem prog_s : (es : List Expr) → ∀ {Λ r ls r0}, SeqTy Γ ρ Λ es r → ValsTy Γ ls →
    (∃ o, Seq ls r0 es o) ∨ DivS ls r0 es
  | [], Λ, r, ls, r0, hty, hls => .inl ⟨_, .nil⟩
  | e :: es, Λ, r, ls, r0, hty, hls => by
    cases hty with
    | one he =>
      rcases prog_e e he hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls₁ r₁ => exact .inl ⟨_, .cons h .nil⟩
        | _ => exact .inl ⟨_, .abrupt h trivial⟩
      · exact .inr (.head hd)
    | cons he hes =>
      rcases prog_e e he hls with ⟨out, h⟩ | hd
      · cases out with
        | ok ls₁ r₁ =>
          cases exec_ty h he hls with
          | ok hls₁ _ =>
            rcases prog_s _ hes hls₁ (r0 := r₁) with ⟨out', h'⟩ | hd
            · exact .inl ⟨_, .cons h h'⟩
            · exact .inr (.tail h hd)
        | _ => exact .inl ⟨_, .abrupt h trivial⟩
      · exact .inr (.head hd)

end


theorem exec_not_div {ls : List WVal} {e : Expr} {o : Out (Option WVal)} (h : Exec ls e o) :
    ¬ DivE ls e := by
  induction h using Exec.rec
    (motive_2 := fun ls es _ _ => ¬ DivA ls es)
    (motive_3 := fun ls r es _ _ => ¬ DivS ls r es)
  case op ih | op_trap ih | op_abrupt ih | br ih | br_abrupt ih | brIf ih | brIf_abrupt ih
      | return_ ih | return_abrupt ih =>
    intro hd; cases hd; contradiction
  case localSet ih | localSet_abrupt ih | localTee ih | localTee_abrupt ih | drop ih
      | drop_abrupt ih | block ih =>
    intro hd; cases hd; contradiction
  case localGet => intro hd; cases hd
  case nop => intro hd; cases hd
  case unreachable => intro hd; cases hd
  case loop hs hx ih =>
    intro hd
    cases hd with
    | loopBody hds => exact ih hds
    | loopBack hs' _ => cases Seq.det hs hs'; cases hx
    | loopInf σ rs h0 hσ => subst h0; cases Seq.det hs (hσ 0); cases hx
  case loop_back hs he ih₁ ih₂ =>
    intro hd
    cases hd with
    | loopBody hds => exact ih₁ hds
    | loopBack hs' hd' => cases Seq.det hs hs'; exact ih₂ hd'
    | loopInf σ rs h0 hσ =>
      subst h0
      cases Seq.det hs (hσ 0)
      exact ih₂ (.loopInf (fun n => σ (n + 1)) (fun n => rs (n + 1)) rfl fun n => hσ (n + 1))
  case if_ hc hb hs hx ih₁ ih₂ =>
    intro hd
    cases hd with
    | ifCond hd' => exact ih₁ hd'
    | ifThen hc' hb' hds =>
      cases Exec.det hc hc'; rw [hb] at hb'; cases hb'; exact ih₂ (by simpa using hds)
    | ifElse hc' hb' hds =>
      cases Exec.det hc hc'; rw [hb] at hb'; cases hb'; exact ih₂ (by simpa using hds)
  case if_abrupt hc hab ih =>
    intro hd
    cases hd with
    | ifCond hd' => exact ih hd'
    | ifThen hc' _ _ => cases Exec.det hc hc'; exact hab
    | ifElse hc' _ _ => cases Exec.det hc hc'; exact hab
  case nil => exact fun hd => nomatch hd
  case cons he ha ih₁ ih₂ =>
    intro hd
    cases hd with
    | head hd' => exact ih₁ hd'
    | tail he' hd' => cases Exec.det he he'; exact ih₂ hd'
  case head_abrupt he hab ih =>
    intro hd
    cases hd with
    | head hd' => exact ih hd'
    | tail he' _ => cases Exec.det he he'; exact hab
  case tail_abrupt he ha _ ih₁ ih₂ =>
    intro hd
    cases hd with
    | head hd' => exact ih₁ hd'
    | tail he' hd' => cases Exec.det he he'; exact ih₂ hd'
  case nil => exact fun hd => nomatch hd
  case cons he hs ih₁ ih₂ =>
    intro hd
    cases hd with
    | head hd' => exact ih₁ hd'
    | tail he' hd' => cases Exec.det he he'; exact ih₂ hd'
  case abrupt he hab ih =>
    intro hd
    cases hd with
    | head hd' => exact ih hd'
    | tail he' _ => cases Exec.det he he'; exact hab


/-- On typed code, the denotation diverges exactly when the run diverges
through a loop: never because of a stuck configuration. -/
theorem den_diverge_iff_divE {E : Silmaril.Games.Sig.{0}} {S : Type 1}
    {Λ : List (Option Silmaril.Wasm.IntType)} {e : Expr} {r : Option Silmaril.Wasm.IntType}
    {ls : List WVal} (hty : Ty Γ ρ Λ e r) (hls : ValsTy Γ ls) (s : S) :
    run' (den e ls : M E S OutE) s = Silmaril.Elgot.ITree.diverge ↔ DivE ls e := by
  rw [(den_exact e ls s).2]
  constructor
  · intro hno
    rcases prog_e e hty hls with ⟨o, h⟩ | hd
    · exact absurd h (hno o)
    · exact hd
  · intro hd o h
    exact exec_not_div h hd


theorem seq_not_div {ls : List WVal} {es : List Expr} {o : Out (Option WVal)}
    (h : Seq ls none es o) : ¬ DivS ls none es := fun hd => by
  obtain ⟨o', hx⟩ := blockExit_none o
  exact exec_not_div (.block (ty := none) h hx) (.block hd)

/-- A typed function on typed arguments runs to an outcome, or its body
diverges through a loop. -/
theorem func_progress {f : FragFunc} {args : List WVal} (hf : funcTyped f)
    (ha : args.map WVal.type = f.params) :
    (∃ o, f.Run args o) ∨ DivS (f.initLocals args) none f.body := by
  rcases f with ⟨ps, lc, res, body⟩
  have hls : ValsTy (ps ++ lc) (args ++ lc.map WVal.zero) := by
    simp only [ValsTy, List.map_append, List.map_map] at ha ⊢
    rw [ha, show (WVal.type ∘ WVal.zero) = id from funext zero_type, List.map_id]
  rcases prog_s body hf hls (r0 := none) with ⟨out, h⟩ | hd
  · have ho := seq_ty h hf hls (fun hb => by subst hb; cases hf; rfl)
    left
    cases ho with
    | ok _ _ => exact ⟨_, ha, _, h, rfl⟩
    | @brk l _ _ _ hl _ _ =>
      cases l with
      | zero => exact ⟨_, ha, _, h, rfl⟩
      | succ l => simp at hl
    | ret _ => exact ⟨_, ha, _, h, rfl⟩
    | trap => exact ⟨_, ha, _, h, rfl⟩
  · exact .inr hd

/-- On a typed function and typed arguments, the abstract body diverges
exactly when the function body diverges through a loop. -/
theorem denFunc_diverge_iff_divS {E : Silmaril.Games.Sig.{0}} {S : Type 1} {f : FragFunc}
    {args : List WVal} (hf : funcTyped f) (ha : args.map WVal.type = f.params) (s : S) :
    run' (denFunc f ⟨args⟩ : M E S _) s = Silmaril.Elgot.ITree.diverge ↔
      DivS (f.initLocals args) none f.body := by
  rw [denFunc_diverge_iff']
  constructor
  · intro hno
    rcases func_progress hf ha with ⟨o, ho⟩ | hd
    · exact absurd ho (hno o)
    · exact hd
  · intro hd o ⟨_, out, h, _⟩
    exact seq_not_div h hd

end Silmaril.Proofs.Wasm.Abstract.FragBody
