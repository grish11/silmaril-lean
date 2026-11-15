module

public import Silmaril.Proofs.Wasm.Abstract.FragBody.Basic

/-!
# The typed fragment: preservation

Typed code on typed locals has typed outcomes: the locals keep their types,
results, branch values and returns have the types of their targets.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FragBody

open Silmaril.Wasm.Abstract.FragBody Silmaril.Wasm.SSA

variable {Γ : List Silmaril.Wasm.IntType} {ρ : Option Silmaril.Wasm.IntType}

theorem OutTy.abrupt {Λ : List (Option Silmaril.Wasm.IntType)} {α β : Type} {P : α → Prop}
    {Q : β → Prop} {o : Out α} (h : OutTy Γ ρ Λ P o) (ha : o.Abrupt) :
    OutTy Γ ρ Λ Q (o.cast : Out β) := by
  cases h with
  | ok => exact ha.elim
  | brk h₁ h₂ h₃ => exact .brk h₁ h₂ h₃
  | ret h => exact .ret h
  | trap => exact .trap

theorem OutTy.abrupt' {Λ : List (Option Silmaril.Wasm.IntType)} {α : Type} {P Q : α → Prop}
    {o : Out α} (h : OutTy Γ ρ Λ P o) (ha : o.Abrupt) : OutTy Γ ρ Λ Q o := by
  cases h with
  | ok => exact ha.elim
  | brk h₁ h₂ h₃ => exact .brk h₁ h₂ h₃
  | ret h => exact .ret h
  | trap => exact .trap

theorem asInt_type {t : Silmaril.Wasm.IntType} {v : WVal} {x : BitVec t.width}
    (h : v.asInt t = some x) : v.type = t := by
  cases t <;> cases v <;> simp_all [WVal.asInt, WVal.type]

theorem ofInt_type (t : Silmaril.Wasm.IntType) (x : BitVec t.width) : (WVal.ofInt t x).type = t := by
  cases t <;> rfl

set_option linter.unusedTactic false in
theorem opSig_eval {o : Op} {ts : List Silmaril.Wasm.IntType} {t : Silmaril.Wasm.IntType}
    {vs : List WVal} {v : WVal} (hs : OpSig o ts t) (hv : ValsTy ts vs)
    (he : o.eval vs = some (.val v)) : v.type = t := by
  cases hs <;> rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _⟩⟩⟩⟩ <;>
    simp_all [ValsTy, Op.eval, UnOp.eval, BinOp.eval]
  all_goals first
    | (obtain ⟨x, -, rfl⟩ := he; first | exact ofInt_type _ _ | rfl)
    | (rcases he with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp_all)
    | (split at he <;> (try split at he)
       all_goals simp only [Option.some.injEq, Res.val.injEq, reduceCtorEq] at he
       all_goals subst he
       all_goals first | exact ofInt_type _ _ | rfl)

theorem valsTy_get {ls : List WVal} {i : Nat} {t : Silmaril.Wasm.IntType} {v : WVal}
    (hl : ValsTy Γ ls) (hg : Γ[i]? = some t) (hv : ls[i]? = some v) : v.type = t := by
  have := congrArg (·[i]?) hl
  simp only [List.getElem?_map, hv, Option.map_some] at this
  rw [hg] at this
  exact Option.some.inj this

theorem valsTy_set {ls : List WVal} {i : Nat} {t : Silmaril.Wasm.IntType} {v : WVal}
    (hl : ValsTy Γ ls) (hg : Γ[i]? = some t) (hv : v.type = t) : ValsTy Γ (ls.set i v) := by
  unfold ValsTy at *
  rw [List.map_set, hl, hv]
  obtain ⟨hi, hgi⟩ := List.getElem?_eq_some_iff.1 hg
  rw [← hgi]; exact List.set_getElem_self hi

theorem valTy_blockRes {ty : Option Silmaril.Wasm.IntType} {r : Option WVal} (h : ValTy ty r) :
    ValTy ty (blockRes ty r) := by
  cases ty <;> simp_all [blockRes, ValTy]

theorem blockExit_ty {Λ : List (Option Silmaril.Wasm.IntType)} {ty : Option Silmaril.Wasm.IntType}
    {o o' : Out (Option WVal)} (h : OutTy Γ ρ (ty :: Λ) (ValTy ty) o) (hx : BlockExit ty o o') :
    OutTy Γ ρ Λ (ValTy ty) o' := by
  cases hx with
  | ok => cases h with | ok h₁ h₂ => exact .ok h₁ (valTy_blockRes h₂)
  | brk0 => cases h with | brk h₀ h₁ h₂ => cases h₀; exact .ok h₁ (valTy_blockRes h₂)
  | brk => cases h with | brk h₀ h₁ h₂ => exact .brk h₀ h₁ h₂
  | ret => cases h with | ret h => exact .ret h
  | trap => exact .trap

theorem loopExit_ty {Λ : List (Option Silmaril.Wasm.IntType)} {ty : Option Silmaril.Wasm.IntType}
    {o o' : Out (Option WVal)} (h : OutTy Γ ρ (none :: Λ) (ValTy ty) o) (hx : LoopExit ty o o') :
    OutTy Γ ρ Λ (ValTy ty) o' := by
  cases hx with
  | ok => cases h with | ok h₁ h₂ => exact .ok h₁ (valTy_blockRes h₂)
  | brk => cases h with | brk h₀ h₁ h₂ => exact .brk h₀ h₁ h₂
  | ret => cases h with | ret h => exact .ret h
  | trap => exact .trap

theorem valTy_head {lt : Option Silmaril.Wasm.IntType} {vs : List WVal} (h : ValsTy lt.toList vs) :
    ValTy lt vs.head? := by
  cases lt <;> cases vs <;> simp_all [ValsTy, ValTy]

theorem valTy_dropLast {lt : Option Silmaril.Wasm.IntType} {vs : List WVal}
    (h : ValsTy (lt.toList ++ [.i32]) vs) : ValTy lt vs.dropLast.head? := by
  cases lt <;> rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;> simp_all [ValsTy, ValTy]

theorem exec_ty {ls : List WVal} {e : Expr} {o : Out (Option WVal)} (h : Exec ls e o) :
    ∀ {Λ r}, Ty Γ ρ Λ e r → ValsTy Γ ls → OutTy Γ ρ Λ (ValTy r) o := by
  induction h using Exec.rec
    (motive_2 := fun ls es o _ => ∀ Λ ts, ArgsTy Γ ρ Λ es ts → ValsTy Γ ls →
      OutTy Γ ρ Λ (ValsTy ts) o)
    (motive_3 := fun ls r0 es o _ => ∀ Λ r, SeqTy Γ ρ Λ es r → ValsTy Γ ls →
      (es = [] → ValTy r r0) → OutTy Γ ρ Λ (ValTy r) o)
  case op hv ih =>
    intro Λ r hty hls
    cases hty with
    | op hs ha =>
      cases ih _ _ ha hls with
      | ok hls' hvs => exact .ok hls' (by simp [ValTy, opSig_eval hs hvs hv])
  case op_trap => intros; exact .trap
  case op_abrupt hab ih =>
    intro Λ r hty hls
    cases hty with
    | op hs ha => exact OutTy.abrupt (ih _ _ ha hls) hab
  case localGet hv =>
    intro Λ r hty hls
    cases hty with
    | localGet hg => exact .ok hls (by simp [ValTy, valsTy_get hls hg hv])
  case localSet ih =>
    intro Λ r hty hls
    cases hty with
    | localSet hg he =>
      cases ih he hls with
      | ok hls' hvt => exact .ok (valsTy_set hls' hg (by simpa [ValTy] using hvt)) rfl
  case localSet_abrupt hab ih =>
    intro Λ r hty hls
    cases hty with
    | localSet hg he => exact OutTy.abrupt' (ih he hls) hab
  case localTee ih =>
    intro Λ r hty hls
    cases hty with
    | localTee hg he =>
      cases ih he hls with
      | ok hls' hvt => exact .ok (valsTy_set hls' hg (by simpa [ValTy] using hvt)) hvt
  case localTee_abrupt hab ih =>
    intro Λ r hty hls
    cases hty with
    | localTee hg he => exact OutTy.abrupt' (ih he hls) hab
  case drop ih =>
    intro Λ r hty hls
    cases hty with
    | drop he => cases ih he hls with | ok hls' _ => exact .ok hls' rfl
  case drop_abrupt hab ih =>
    intro Λ r hty hls
    cases hty with
    | drop he => exact OutTy.abrupt' (ih he hls) hab
  case nop => intro Λ r hty hls; cases hty; exact .ok hls rfl
  case unreachable => intros; exact .trap
  case block hx ih =>
    intro Λ r hty hls
    cases hty with
    | block hb => exact blockExit_ty (ih _ _ hb hls fun h => by subst h; cases hb; rfl) hx
  case loop hx ih =>
    intro Λ r hty hls
    cases hty with
    | loop hb => exact loopExit_ty (ih _ _ hb hls fun h => by subst h; cases hb; rfl) hx
  case loop_back ih₁ ih₂ =>
    intro Λ r hty hls
    have hty' := hty
    cases hty with
    | loop hb =>
      cases ih₁ _ _ hb hls fun h => by subst h; cases hb; rfl with
      | brk _ hls' _ => exact ih₂ hty' hls'
  case if_ b _ _ _ hb _ hx ih₁ ih₂ =>
    intro Λ r hty hls
    cases hty with
    | if_ hc ht he =>
      cases ih₁ hc hls with
      | ok hls₁ _ =>
        cases b
        · exact blockExit_ty (ih₂ _ _ he hls₁ fun h => by simp at h; subst h; cases he; rfl) hx
        · exact blockExit_ty (ih₂ _ _ ht hls₁ fun h => by simp at h; subst h; cases ht; rfl) hx
  case if_abrupt hab ih =>
    intro Λ r hty hls
    cases hty with
    | if_ hc _ _ => exact OutTy.abrupt' (ih hc hls) hab
  case br ih =>
    intro Λ r hty hls
    cases hty with
    | br hl ha => cases ih _ _ ha hls with | ok hls' hvs => exact .brk hl hls' (valTy_head hvs)
  case br_abrupt hab ih =>
    intro Λ r hty hls
    cases hty with
    | br hl ha => exact OutTy.abrupt (ih _ _ ha hls) hab
  case brIf ls ls' l args vs c b _ hc hb ih =>
    intro Λ r hty hls
    cases hty with
    | brIf hl ha =>
      cases ih _ _ ha hls with
      | ok hls' hvs =>
        cases b
        · exact .ok hls' (valTy_dropLast hvs)
        · exact .brk hl hls' (valTy_dropLast hvs)
  case brIf_abrupt hab ih =>
    intro Λ r hty hls
    cases hty with
    | brIf hl ha => exact OutTy.abrupt (ih _ _ ha hls) hab
  case return_ ih =>
    intro Λ r hty hls
    cases hty with
    | return_ ha => cases ih _ _ ha hls with | ok _ hvs => exact .ret (valTy_head hvs)
  case return_abrupt hab ih =>
    intro Λ r hty hls
    cases hty with
    | return_ ha => exact OutTy.abrupt (ih _ _ ha hls) hab
  case nil Λ ts hty hls => cases hty; exact .ok hls rfl
  case cons ih₁ ih₂ Λ ts hty hls =>
    cases hty with
    | cons he hes =>
      cases ih₁ he hls with
      | ok hls₁ hv =>
        cases ih₂ _ _ hes hls₁ with
        | ok hls₂ hvs => exact .ok hls₂ (by simp_all [ValsTy, ValTy])
  case head_abrupt hab ih Λ ts hty hls =>
    cases hty with
    | cons he _ => exact OutTy.abrupt (ih he hls) hab
  case tail_abrupt hab ih₁ ih₂ Λ ts hty hls =>
    cases hty with
    | cons he hes =>
      cases ih₁ he hls with
      | ok hls₁ _ => exact OutTy.abrupt' (ih₂ _ _ hes hls₁) hab
  case nil ls₀ r₀ Λ r hty => intro hls hr; exact .ok hls (hr rfl)
  case cons _ h₂ ih₁ ih₂ Λ r hty hls =>
    intro hr
    cases hty with
    | one he =>
      cases ih₁ he hls with
      | ok hls₁ hv => cases h₂; exact .ok hls₁ hv
    | cons he hes =>
      cases ih₁ he hls with
      | ok hls₁ _ => exact ih₂ _ _ hes hls₁ (fun h => by cases h)
  case abrupt hab ih Λ r hty hls hr =>
    cases hty with
    | one he => exact OutTy.abrupt' (ih he hls) hab
    | cons he _ => exact OutTy.abrupt' (ih he hls) hab


theorem seq_ty {Λ : List (Option Silmaril.Wasm.IntType)} :
    ∀ {es : List Expr} {ls : List WVal} {r0 : Option WVal} {o : Out (Option WVal)}
      {r : Option Silmaril.Wasm.IntType}, Seq ls r0 es o → SeqTy Γ ρ Λ es r → ValsTy Γ ls →
      (es = [] → ValTy r r0) → OutTy Γ ρ Λ (ValTy r) o
  | [], ls, r0, o, r, h, _, hls, hr => by cases h; exact .ok hls (hr rfl)
  | e :: es, ls, r0, o, r, h, hty, hls, _ => by
    cases h with
    | cons he hs =>
      cases hty with
      | one hte => cases exec_ty he hte hls with | ok hls₁ hv => cases hs; exact .ok hls₁ hv
      | cons hte htes => cases exec_ty he hte hls with
        | ok hls₁ _ => exact seq_ty hs htes hls₁ (fun h => by cases h)
    | abrupt he hab =>
      cases hty with
      | one hte => exact OutTy.abrupt' (exec_ty he hte hls) hab
      | cons hte _ => exact OutTy.abrupt' (exec_ty he hte hls) hab

/-- A typed fragment function on typed arguments returns a value of its
result type. -/
theorem zero_type (t : Silmaril.Wasm.IntType) : (WVal.zero t).type = t := by cases t <;> rfl

theorem run_ty {f : FragFunc} {args : List WVal} {r : Option WVal} (hf : funcTyped f)
    (h : f.Run args (.ret r)) : ValTy f.result r := by
  rcases f with ⟨ps, lc, res, body⟩
  obtain ⟨ha, out, hs, he⟩ := h
  have hls : ValsTy (ps ++ lc) (args ++ lc.map WVal.zero) := by
    simp only [ValsTy, List.map_append, List.map_map] at ha ⊢
    rw [ha, show (WVal.type ∘ WVal.zero) = id from funext zero_type, List.map_id]
  have ho := seq_ty hs hf hls (fun hb => by subst hb; cases hf; rfl)
  cases ho with
  | ok _ hv =>
    simp only [funcExit, Option.some.injEq, FOut.ret.injEq] at he; subst he
    exact valTy_blockRes hv
  | @brk l _ _ _ hl _ hv =>
    cases l with
    | zero =>
      simp only [funcExit, Option.some.injEq, FOut.ret.injEq] at he; subst he
      simp at hl; subst hl; exact valTy_blockRes hv
    | succ l => simp [funcExit] at he
  | ret hv =>
    simp only [funcExit, Option.some.injEq, FOut.ret.injEq] at he; subst he
    exact valTy_blockRes hv
  | trap => simp [funcExit] at he

end Silmaril.Proofs.Wasm.Abstract.FragBody
