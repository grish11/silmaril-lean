module

public import Silmaril.Wasm.Abstract.FragBody.Defs
public import Silmaril.Wasm.Abstract.Body.Thms
public import Silmaril.Wasm.Abstract.BodyTrace.Thms
public import Silmaril.Wasm.SSA.Fragment.Thms

/-!
# The fragment denotation: adequacy against the big-step semantics

Every derivation of `Exec`, `Args`, `Seq` is computed by the denotation
(`exec_den`), and the denotation of every expression either diverges or is
the outcome of a derivation (`den_good`). Loops use the iteration of trees
without events (`BodyTrace.iter_pure`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FragBody

open Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.Abstract.BodyTrace
  Silmaril.Wasm.Abstract.FragBody Silmaril.Wasm.SSA Silmaril.Elgot.ITree

variable {E : Sig.{0}} {S : Type 1}

/-- A body run from a state, as an interaction tree. -/
noncomputable abbrev run' {X : Type 1} (x : M E S X) (s : S) :
    Tree (SigEv E) (Except PUnit.{2} (X × S)) := (x.run s).run

theorem run_pure {X : Type 1} (x : X) (s : S) : run' (pure x : M E S X) s = ret (.ok (x, s)) := rfl

theorem run_trap {X : Type 1} (s : S) : run' (trap ⟨⟩ : M E S X) s = ret (.error ⟨⟩) := by
  simp [trap, throw, throwThe, MonadExceptOf.throw, StateT.lift, ExceptT.run,
    ExceptT.mk, Functor.map, ExceptT.map, StateT.run]
  rfl

theorem run_stuck {X : Type 1} (s : S) : run' (stuck : M E S X) s = diverge := rfl

theorem run_fin {α : Type} (o : Out α) (s : S) : run' (fin o : M E S _) s = outTree o s := by
  cases o <;> first | exact run_trap s | rfl

theorem run_bind {X Y : Type 1} (x : M E S X) (k : X → M E S Y) (s : S) :
    run' (x >>= k) s = run' x s >>= fun r =>
      match r with
      | .ok (a, s') => run' (k a) s'
      | .error e => pure (.error e) := by
  change ((x >>= k).run s).run = _
  rw [StateT.run_bind, ExceptT.run_bind]
  congr 1
  funext r
  rcases r with e | ⟨a, s'⟩ <;> rfl

theorem run_bind_ok {X Y : Type 1} {x : M E S X} {k : X → M E S Y} {s s' : S} {a : X}
    (h : run' x s = ret (.ok (a, s'))) : run' (x >>= k) s = run' (k a) s' := by
  rw [run_bind, h]; exact pure_bind _ _

theorem run_bind_error {X Y : Type 1} {x : M E S X} {k : X → M E S Y} {s : S}
    (h : run' x s = ret (.error ⟨⟩)) : run' (x >>= k) s = ret (.error ⟨⟩) := by
  rw [run_bind, h]; exact pure_bind _ _

theorem run_bind_diverge {X Y : Type 1} {x : M E S X} {k : X → M E S Y} {s : S}
    (h : run' x s = diverge) : run' (x >>= k) s = diverge := by
  rw [run_bind, h, diverge_bind]

/-- Bind after an outcome. -/
theorem run_bind_encT {α : Type} {Y : Type 1} {x : M E S (ULift.{1} (Out α))}
    {k : ULift.{1} (Out α) → M E S Y} {s : S} {o : Out α} (h : run' x s = outTree o s) :
    run' (x >>= k) s = match o with
      | .trap => ret (.error ⟨⟩)
      | o => run' (k ⟨o⟩) s := by
  cases o <;> first | exact run_bind_error h | exact run_bind_ok h

theorem loop_unfold (ty : Option Silmaril.Wasm.IntType) (body : List Expr) (ls : List WVal) :
    (den (.loop ty body) ls : M E S OutE) =
      ((denSeq body ls none >>= fun r => loopK ty r.down) >>= Sum.elim pure
        fun l : Loc => den (.loop ty body) l.down) := by
  rw [den]
  refine (congrFun (Silmaril.Elgot.LawfulElgotMonad.fixpoint (m := M E S)
    (fun l : Loc => denSeq body l.down none >>= fun r => loopK ty r.down)) ⟨ls⟩).trans ?_
  congr 1

theorem blockK_ok {ty : Option Silmaril.Wasm.IntType} {o o' : Out (Option WVal)}
    (h : BlockExit ty o o') (s : S) : run' (blockK ty o : M E S OutE) s = outTree o' s := by
  cases h with
  | ok hb | brk0 hb =>
    simp only [blockK, exitOk]
    split_ifs with hc
    · cases ty <;> cases ‹Option WVal› <;> simp_all [BlockOk]
    · rfl
  | brk => rfl
  | ret => rfl
  | trap => exact run_trap s

theorem block_bind {ty : Option Silmaril.Wasm.IntType} {x : M E S OutE} {s : S}
    {out out' : Out (Option WVal)} (h : run' x s = outTree out s) (hx : BlockExit ty out out') :
    run' (x >>= fun r => blockK ty r.down) s = outTree out' s := by
  rcases hx with hb | hb | _ | _ | _
  · rw [run_bind_ok h]; exact blockK_ok (.ok hb) s
  · rw [run_bind_ok h]; exact blockK_ok (.brk0 hb) s
  · rw [run_bind_ok h]; rfl
  · rw [run_bind_ok h]; rfl
  · rw [run_bind_error h]; rfl

theorem exitOk_ok {ty : Option Silmaril.Wasm.IntType} {ls : List WVal} {r : Option WVal}
    (hb : BlockOk ty r) : (exitOk ty ls r : M E S OutE) = pure ⟨.ok ls (blockRes ty r)⟩ := by
  simp only [exitOk]
  split_ifs with hc
  · cases ty <;> cases r <;> simp_all [BlockOk]
  · rfl

theorem exec_den {ls : List WVal} {e : Expr} {o : Out (Option WVal)} (h : Exec ls e o) (s : S) :
    run' (den e ls : M E S OutE) s = outTree o s := by
  revert s
  induction h using Exec.rec
    (motive_2 := fun ls es o _ => ∀ s : S, run' (denArgs es ls : M E S OutL) s = outTree o s)
    (motive_3 := fun ls r es o _ => ∀ s : S, run' (denSeq es ls r : M E S OutE) s = outTree o s)
  case op hv ih =>
    intro s; simp only [den]; rw [run_bind_ok (ih s)]; simp only [opK, hv]; rfl
  case op_trap hv ih =>
    intro s; simp only [den]; rw [run_bind_ok (ih s)]; simp only [opK, hv]; exact run_trap s
  case op_abrupt out _ hab ih =>
    intro s; simp only [den]
    cases out with
    | ok => exact hab.elim
    | trap => rw [run_bind_error (ih s)]; rfl
    | brk => rw [run_bind_ok (ih s)]; rfl
    | ret => rw [run_bind_ok (ih s)]; rfl
  case localGet hv => intro s; simp only [den, hv]; rfl
  case localSet ih | localTee ih =>
    intro s; simp only [den]; rw [run_bind_ok (ih s)]; rfl
  case drop ih => intro s; simp only [den]; rw [run_bind_ok (ih s)]; rfl
  case localSet_abrupt out _ hab ih | localTee_abrupt out _ hab ih | drop_abrupt out _ hab ih =>
    intro s; simp only [den]
    cases out with
    | ok => exact hab.elim
    | trap => rw [run_bind_error (ih s)]; rfl
    | brk => rw [run_bind_ok (ih s)]; rfl
    | ret => rw [run_bind_ok (ih s)]; rfl
  case nop => intro s; rfl
  case unreachable => intro s; exact run_trap s
  case block hx ih => intro s; simp only [den]; exact block_bind (ih s) hx
  case loop ls ty body out out' _ hx ih =>
    intro s; rw [loop_unfold]
    cases hx with
    | @ok ls' r' hb =>
      have h1 : run' (denSeq body ls none >>= fun r => loopK ty r.down : M E S (OutE ⊕ Loc)) s =
          ret (.ok (.inl ⟨.ok ls' (blockRes ty r')⟩, s)) := by
        rw [run_bind_ok (ih s)]; simp only [loopK, exitOk_ok hb, pure_bind]; rfl
      rw [run_bind_ok h1]; rfl
    | @brk l ls' r' =>
      have h1 : run' (denSeq body ls none >>= fun r => loopK ty r.down : M E S (OutE ⊕ Loc)) s =
          ret (.ok (.inl ⟨.brk l ls' r'⟩, s)) := by
        rw [run_bind_ok (ih s)]; rfl
      rw [run_bind_ok h1]; rfl
    | @ret r' =>
      have h1 : run' (denSeq body ls none >>= fun r => loopK ty r.down : M E S (OutE ⊕ Loc)) s =
          ret (.ok (.inl ⟨.ret r'⟩, s)) := by
        rw [run_bind_ok (ih s)]; rfl
      rw [run_bind_ok h1]; rfl
    | trap => rw [run_bind_error (run_bind_error (ih s))]; rfl
  case loop_back ls ls' ty body r out _ _ ih₁ ih₂ =>
    intro s; rw [loop_unfold]
    have h1 : run' (denSeq body ls none >>= fun r => loopK ty r.down : M E S (OutE ⊕ Loc)) s =
        ret (.ok (.inr ⟨ls'⟩, s)) := by
      rw [run_bind_ok (ih₁ s)]; rfl
    rw [run_bind_ok h1]; exact ih₂ s
  case if_ ls ls₁ ty c t e cv b out out' _ hb _ hx ih₁ ih₂ =>
    intro s; simp only [den]; rw [run_bind_ok (ih₁ s)]
    simp only [hb]
    have := ih₂ s
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at this; exact block_bind this hx
    · simp only [↓reduceIte] at this; exact block_bind this hx
  case if_abrupt out _ hab ih =>
    intro s; simp only [den]
    cases out with
    | ok => exact hab.elim
    | trap => rw [run_bind_error (ih s)]; rfl
    | brk => rw [run_bind_ok (ih s)]; rfl
    | ret => rw [run_bind_ok (ih s)]; rfl
  case br ih => intro s; simp only [den]; rw [run_bind_ok (ih s)]; rfl
  case br_abrupt out _ hab ih | brIf_abrupt out _ hab ih | return_abrupt out _ hab ih =>
    intro s; simp only [den]
    cases out with
    | ok => exact hab.elim
    | trap => rw [run_bind_error (ih s)]; rfl
    | brk => rw [run_bind_ok (ih s)]; rfl
    | ret => rw [run_bind_ok (ih s)]; rfl
  case brIf hc hb ih =>
    intro s; simp only [den]; rw [run_bind_ok (ih s)]; simp only [brIfK, hc, hb]
    split <;> rfl
  case return_ ih => intro s; simp only [den]; rw [run_bind_ok (ih s)]; rfl
  case nil => rfl
  case cons ih₁ ih₂ s =>
    simp only [denArgs]; rw [run_bind_ok (ih₁ s)]; simp only
    rw [run_bind_ok (ih₂ s)]; rfl
  case head_abrupt out _ hab ih s =>
    simp only [denArgs]
    cases out with
    | ok => exact hab.elim
    | trap => rw [run_bind_error (ih s)]; rfl
    | brk => rw [run_bind_ok (ih s)]; rfl
    | ret => rw [run_bind_ok (ih s)]; rfl
  case tail_abrupt out _ _ hab ih₁ ih₂ s =>
    simp only [denArgs]; rw [run_bind_ok (ih₁ s)]; simp only
    cases out with
    | ok => exact hab.elim
    | trap => rw [run_bind_error (ih₂ s)]; rfl
    | brk => rw [run_bind_ok (ih₂ s)]; rfl
    | ret => rw [run_bind_ok (ih₂ s)]; rfl
  case nil => intro _; rfl
  case cons ih₁ ih₂ s =>
    simp only [denSeq]; rw [run_bind_ok (ih₁ s)]; exact ih₂ s
  case abrupt out _ hab ih s =>
    simp only [denSeq]
    cases out with
    | ok => exact hab.elim
    | trap => rw [run_bind_error (ih s)]; rfl
    | brk => rw [run_bind_ok (ih s)]; rfl
    | ret => rw [run_bind_ok (ih s)]; rfl

/-! ## Every denotation is a derivation or diverges -/

/-- A body that diverges or computes an outcome satisfying `P`. -/
def Good {α : Type} (x : M E S (ULift.{1} (Out α))) (s : S) (P : Out α → Prop) : Prop :=
  run' x s = diverge ∨ ∃ o, P o ∧ run' x s = outTree o s

theorem exitOk_cases (ty : Option Silmaril.Wasm.IntType) (ls : List WVal) (r : Option WVal) :
    (exitOk ty ls r : M E S OutE) = stuck ∨
      (BlockOk ty r ∧ (exitOk ty ls r : M E S OutE) = pure ⟨.ok ls (blockRes ty r)⟩) := by
  by_cases hb : BlockOk ty r
  · exact .inr ⟨hb, exitOk_ok hb⟩
  · left
    simp only [exitOk]
    split_ifs with hc
    · rfl
    · exfalso; apply hb; cases ty <;> cases r <;> simp_all [BlockOk]

theorem block_good {ty : Option Silmaril.Wasm.IntType} {x : M E S OutE} {s : S}
    {out : Out (Option WVal)} (h : run' x s = outTree out s) :
    Good (x >>= fun r => blockK ty r.down) s (BlockExit ty out) := by
  cases out with
  | trap => exact .inr ⟨.trap, .trap, run_bind_error h⟩
  | ret r => exact .inr ⟨.ret r, .ret, (run_bind_ok h).trans rfl⟩
  | brk l ls r =>
    cases l with
    | succ l => exact .inr ⟨.brk l ls r, .brk, (run_bind_ok h).trans rfl⟩
    | zero =>
      rw [Good, run_bind_ok h]
      rcases exitOk_cases (E := E) (S := S) ty ls r with he | ⟨hb, he⟩
      · exact .inl (by simp only [blockK, he]; rfl)
      · exact .inr ⟨_, .brk0 hb, by simp only [blockK, he]; rfl⟩
  | ok ls r =>
    rw [Good, run_bind_ok h]
    rcases exitOk_cases (E := E) (S := S) ty ls r with he | ⟨hb, he⟩
    · exact .inl (by simp only [blockK, he]; rfl)
    · exact .inr ⟨_, .ok hb, by simp only [blockK, he]; rfl⟩

/-- The value of an outcome tree. -/
def encV {α : Type} (o : Out α) (s : S) : Except PUnit.{2} (ULift.{1} (Out α) × S) :=
  match o with
  | .trap => .error ⟨⟩
  | o => .ok (⟨o⟩, s)

theorem encT_eq {α : Type} (o : Out α) (s : S) : (outTree o s : Tree (SigEv E) _) = ret (encV o s) := by
  cases o <;> rfl

/-- One iteration of a loop body, at the tree level. -/
noncomputable abbrev loopG (ty : Option Silmaril.Wasm.IntType) (body : List Expr) :
    Loc × S → Tree (SigEv E) (Except PUnit.{2} (OutE × S) ⊕ (Loc × S)) :=
  loopTree (fun l : Loc => (denSeq body l.down none >>= fun r => loopK ty r.down : M E S (OutE ⊕ Loc)))

theorem loopG_of {ty : Option Silmaril.Wasm.IntType} {body : List Expr} {p : Loc × S}
    {v : Except PUnit.{2} ((OutE ⊕ Loc) × S)}
    (h : run' (denSeq body p.1.down none >>= fun r => loopK ty r.down : M E S (OutE ⊕ Loc)) p.2 =
      ret v) : loopG (E := E) ty body p = ret (loopEnd v) := by
  show run' _ p.2 >>= _ = _
  rw [h]; exact pure_bind _ _

theorem loopG_spec (ty : Option Silmaril.Wasm.IntType) (body : List Expr)
    (ih : ∀ (ls : List WVal) (s : S), Good (denSeq body ls none : M E S OutE) s (Seq ls none body))
    (p : Loc × S) :
    loopG (E := E) ty body p = diverge ∨
      (∃ ls' r, Seq p.1.down none body (.brk 0 ls' r) ∧
        loopG (E := E) ty body p = ret (.inr (⟨ls'⟩, p.2))) ∨
      ∃ o, (∃ out, Seq p.1.down none body out ∧ LoopExit ty out o) ∧
        loopG (E := E) ty body p = ret (.inl (encV o p.2)) := by
  rcases ih p.1.down p.2 with hd | ⟨out, hseq, h⟩
  · left
    show run' _ p.2 >>= _ = _
    rw [run_bind_diverge hd, diverge_bind]
  · cases out with
    | trap =>
      exact .inr (.inr ⟨.trap, ⟨_, hseq, .trap⟩, loopG_of (run_bind_error h)⟩)
    | ret r =>
      exact .inr (.inr ⟨.ret r, ⟨_, hseq, .ret⟩, loopG_of ((run_bind_ok h).trans rfl)⟩)
    | brk l ls' r =>
      cases l with
      | zero => exact .inr (.inl ⟨ls', r, hseq, loopG_of ((run_bind_ok h).trans rfl)⟩)
      | succ l =>
        exact .inr (.inr ⟨.brk l ls' r, ⟨_, hseq, .brk⟩, loopG_of ((run_bind_ok h).trans rfl)⟩)
    | ok ls' r =>
      rcases exitOk_cases (E := E) (S := S) ty ls' r with he | ⟨hb, he⟩
      · left
        show run' _ p.2 >>= _ = _
        have : run' (denSeq body p.1.down none >>= fun r => loopK ty r.down : M E S (OutE ⊕ Loc))
            p.2 = diverge := by
          rw [run_bind_ok h]; simp only [loopK, he]; exact run_bind_diverge (run_stuck _)
        rw [this, diverge_bind]
      · refine .inr (.inr ⟨.ok ls' (blockRes ty r), ⟨_, hseq, .ok hb⟩,
          (loopG_of (v := .ok (.inl ⟨.ok ls' (blockRes ty r)⟩, p.2)) ?_).trans rfl⟩)
        rw [run_bind_ok h]; simp only [loopK, he, pure_bind]; rfl

theorem loop_good (ty : Option Silmaril.Wasm.IntType) (body : List Expr)
    (ih : ∀ (ls : List WVal) (s : S), Good (denSeq body ls none : M E S OutE) s (Seq ls none body))
    (ls : List WVal) (s : S) :
    Good (den (.loop ty body) ls : M E S OutE) s (Exec ls (.loop ty body)) := by
  have hrun : run' (den (.loop ty body) ls : M E S OutE) s =
      (Silmaril.Elgot.iter (loopG (E := E) ty body) (⟨ls⟩, s) : Tree (SigEv E) _) := by
    simp only [den]; exact run_iter _ _ _
  have hpure : ∀ p, loopG (E := E) ty body p = diverge ∨ ∃ v, loopG (E := E) ty body p = ret v :=
    fun p => by
      rcases loopG_spec ty body ih p with h | ⟨_, _, _, h⟩ | ⟨_, _, h⟩
      · exact .inl h
      · exact .inr ⟨_, h⟩
      · exact .inr ⟨_, h⟩
  have key : ∀ (p : Loc × S) (y : Except PUnit.{2} (OutE × S)), PureReach (loopG (E := E) ty body) p y →
      ∃ o, Exec p.1.down (.loop ty body) o ∧ y = encV o p.2 := by
    intro p y hr
    induction hr with
    | @done p y hx =>
      rcases loopG_spec ty body ih p with h | ⟨_, _, _, h⟩ | ⟨o, ⟨out, hseq, hex⟩, h⟩
      · rw [h] at hx; exact absurd hx.symm (ret_ne_diverge _)
      · rw [h] at hx; cases ret_inj.1 hx
      · rw [h] at hx; cases ret_inj.1 hx; exact ⟨o, .loop hseq hex, rfl⟩
    | @step p x' y hx _ ihr =>
      rcases loopG_spec ty body ih p with h | ⟨ls', r, hseq, h⟩ | ⟨o, _, h⟩
      · rw [h] at hx; exact absurd hx.symm (ret_ne_diverge _)
      · rw [h] at hx; cases ret_inj.1 hx
        obtain ⟨o, hex, rfl⟩ := ihr
        exact ⟨o, .loop_back hseq hex, rfl⟩
      · rw [h] at hx; cases ret_inj.1 hx
  rcases iter_pure hpure (⟨ls⟩, s) with ⟨y, hr, hy⟩ | ⟨hd, -⟩
  · obtain ⟨o, hex, rfl⟩ := key _ _ hr
    exact .inr ⟨o, hex, by rw [hrun, hy, encT_eq]⟩
  · exact .inl (hrun.trans hd)

mutual

theorem den_good : (e : Expr) → (ls : List WVal) → (s : S) →
    Good (den e ls : M E S OutE) s (Exec ls e)
  | .op o args, ls, s => by
    simp only [Good, den]
    rcases denArgs_good args ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls' vs =>
        rw [run_bind_ok h]
        cases hv : o.eval vs with
        | none => exact .inl (by simp only [opK, hv]; rfl)
        | some r =>
          cases r with
          | val v => exact .inr ⟨_, .op ho hv, by simp only [opK, hv]; rfl⟩
          | trap => exact .inr ⟨_, .op_trap ho hv, by simp only [opK, hv]; exact run_trap s⟩
      | trap => exact .inr ⟨_, .op_abrupt ho trivial, run_bind_error h⟩
      | brk l ls' r => exact .inr ⟨_, .op_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r => exact .inr ⟨_, .op_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
  | .localGet i, ls, s => by
    simp only [Good, den]
    cases hi : ls[i]? with
    | none => exact .inl rfl
    | some v => exact .inr ⟨_, .localGet hi, rfl⟩
  | .localSet i e, ls, s => by
    simp only [Good, den]
    rcases den_good e ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls' r =>
        cases r with
        | none => exact .inl ((run_bind_ok h).trans rfl)
        | some v => exact .inr ⟨_, .localSet ho, (run_bind_ok h).trans rfl⟩
      | trap => exact .inr ⟨_, .localSet_abrupt ho trivial, run_bind_error h⟩
      | brk l ls' r => exact .inr ⟨_, .localSet_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r => exact .inr ⟨_, .localSet_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
  | .localTee i e, ls, s => by
    simp only [Good, den]
    rcases den_good e ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls' r =>
        cases r with
        | none => exact .inl ((run_bind_ok h).trans rfl)
        | some v => exact .inr ⟨_, .localTee ho, (run_bind_ok h).trans rfl⟩
      | trap => exact .inr ⟨_, .localTee_abrupt ho trivial, run_bind_error h⟩
      | brk l ls' r => exact .inr ⟨_, .localTee_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r => exact .inr ⟨_, .localTee_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
  | .drop e, ls, s => by
    simp only [Good, den]
    rcases den_good e ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls' r => exact .inr ⟨_, .drop ho, (run_bind_ok h).trans rfl⟩
      | trap => exact .inr ⟨_, .drop_abrupt ho trivial, run_bind_error h⟩
      | brk l ls' r => exact .inr ⟨_, .drop_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r => exact .inr ⟨_, .drop_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
  | .nop, ls, s => .inr ⟨_, .nop, rfl⟩
  | .unreachable, ls, s => .inr ⟨_, .unreachable, run_trap s⟩
  | .block ty body, ls, s => by
    simp only [den]
    rcases denSeq_good body ls none s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · rcases block_good (ty := ty) h with hd | ⟨o2, hx, h2⟩
      · exact .inl hd
      · exact .inr ⟨o2, .block ho hx, h2⟩
  | .loop ty body, ls, s => loop_good ty body (fun ls s => denSeq_good body ls none s) ls s
  | .if_ ty c t e, ls, s => by
    simp only [Good, den]
    rcases den_good c ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls₁ r =>
        rw [run_bind_ok h]
        cases r with
        | none => exact .inl rfl
        | some cv =>
          cases hb : cv.truthy with
          | none => exact .inl (by simp only [hb]; rfl)
          | some b =>
            cases b
            · simp only [hb]
              rcases denSeq_good e ls₁ none s with hd | ⟨o2, ho2, h2⟩
              · exact .inl (run_bind_diverge hd)
              · rcases block_good (ty := ty) h2 with hd | ⟨o3, hx, h3⟩
                · exact .inl hd
                · exact .inr ⟨o3, .if_ ho hb (by simpa using ho2) hx, h3⟩
            · simp only [hb]
              rcases denSeq_good t ls₁ none s with hd | ⟨o2, ho2, h2⟩
              · exact .inl (run_bind_diverge hd)
              · rcases block_good (ty := ty) h2 with hd | ⟨o3, hx, h3⟩
                · exact .inl hd
                · exact .inr ⟨o3, .if_ ho hb (by simpa using ho2) hx, h3⟩
      | trap => exact .inr ⟨_, .if_abrupt ho trivial, run_bind_error h⟩
      | brk l ls' r => exact .inr ⟨_, .if_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r => exact .inr ⟨_, .if_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
  | .br l args, ls, s => by
    simp only [Good, den]
    rcases denArgs_good args ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls' vs => exact .inr ⟨_, .br ho, (run_bind_ok h).trans rfl⟩
      | trap => exact .inr ⟨_, .br_abrupt ho trivial, run_bind_error h⟩
      | brk l' ls' r => exact .inr ⟨_, .br_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r => exact .inr ⟨_, .br_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
  | .brIf l args, ls, s => by
    simp only [Good, den]
    rcases denArgs_good args ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls' vs =>
        rw [run_bind_ok h]
        cases hc : vs.getLast? with
        | none => exact .inl (by simp only [brIfK, hc]; rfl)
        | some c =>
          cases hb : c.truthy with
          | none => exact .inl (by simp only [brIfK, hc, hb]; rfl)
          | some b =>
            refine .inr ⟨_, .brIf ho hc hb, ?_⟩
            simp only [brIfK, hc, hb]
            cases b <;> rfl
      | trap => exact .inr ⟨_, .brIf_abrupt ho trivial, run_bind_error h⟩
      | brk l' ls' r => exact .inr ⟨_, .brIf_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r => exact .inr ⟨_, .brIf_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
  | .return_ args, ls, s => by
    simp only [Good, den]
    rcases denArgs_good args ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls' vs => exact .inr ⟨_, .return_ ho, (run_bind_ok h).trans rfl⟩
      | trap => exact .inr ⟨_, .return_abrupt ho trivial, run_bind_error h⟩
      | brk l' ls' r => exact .inr ⟨_, .return_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r => exact .inr ⟨_, .return_abrupt ho trivial, (run_bind_ok h).trans rfl⟩

theorem denArgs_good : (es : List Expr) → (ls : List WVal) → (s : S) →
    Good (denArgs es ls : M E S OutL) s (Args ls es)
  | [], ls, s => .inr ⟨_, .nil, rfl⟩
  | e :: es, ls, s => by
    simp only [Good, denArgs]
    rcases den_good e ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls₁ r =>
        rw [run_bind_ok h]
        cases r with
        | none => exact .inl rfl
        | some v =>
          simp only
          rcases denArgs_good es ls₁ s with hd | ⟨o2, ho2, h2⟩
          · exact .inl (run_bind_diverge hd)
          · cases o2 with
            | ok ls₂ vs => exact .inr ⟨_, .cons ho ho2, (run_bind_ok h2).trans rfl⟩
            | trap => exact .inr ⟨_, .tail_abrupt ho ho2 trivial, run_bind_error h2⟩
            | brk l ls₂ r => exact .inr ⟨_, .tail_abrupt ho ho2 trivial, (run_bind_ok h2).trans rfl⟩
            | ret r => exact .inr ⟨_, .tail_abrupt ho ho2 trivial, (run_bind_ok h2).trans rfl⟩
      | trap => exact .inr ⟨_, .head_abrupt ho trivial, run_bind_error h⟩
      | brk l ls' r => exact .inr ⟨_, .head_abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r => exact .inr ⟨_, .head_abrupt ho trivial, (run_bind_ok h).trans rfl⟩

theorem denSeq_good : (es : List Expr) → (ls : List WVal) → (r : Option WVal) → (s : S) →
    Good (denSeq es ls r : M E S OutE) s (Seq ls r es)
  | [], ls, r, s => .inr ⟨_, .nil, rfl⟩
  | e :: es, ls, r, s => by
    simp only [Good, denSeq]
    rcases den_good e ls s with hd | ⟨o', ho, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases o' with
      | ok ls₁ r₁ =>
        rw [run_bind_ok h]
        rcases denSeq_good es ls₁ r₁ s with hd | ⟨o2, ho2, h2⟩
        · exact .inl hd
        · exact .inr ⟨_, .cons ho ho2, h2⟩
      | trap => exact .inr ⟨_, .abrupt ho trivial, run_bind_error h⟩
      | brk l ls' r' => exact .inr ⟨_, .abrupt ho trivial, (run_bind_ok h).trans rfl⟩
      | ret r' => exact .inr ⟨_, .abrupt ho trivial, (run_bind_ok h).trans rfl⟩

end

/-! ## Exactness -/

theorem encT_inj {α : Type} {o o' : Out α} {s : S}
    (h : (outTree o s : Tree (SigEv E) _) = outTree o' s) : o = o' := by
  rw [encT_eq, encT_eq, ret_inj] at h
  cases o <;> cases o' <;> simp_all [encV]

theorem encT_ne_diverge {α : Type} (o : Out α) (s : S) :
    (outTree o s : Tree (SigEv E) _) ≠ diverge := by
  rw [encT_eq]; exact ret_ne_diverge _

theorem den_exact (e : Expr) (ls : List WVal) (s : S) :
    (∀ o, Exec ls e o ↔ run' (den e ls : M E S OutE) s = outTree o s) ∧
      (run' (den e ls : M E S OutE) s = diverge ↔ ∀ o, ¬ Exec ls e o) := by
  refine ⟨fun o => ⟨fun h => exec_den h s, fun h => ?_⟩, ⟨fun h o ho => ?_, fun h => ?_⟩⟩
  · rcases den_good e ls s with hd | ⟨o', ho', h'⟩
    · exact absurd (h.symm.trans hd) (encT_ne_diverge o s)
    · rw [encT_inj (h.symm.trans h')]; exact ho'
  · exact encT_ne_diverge o s ((exec_den ho s).symm.trans h)
  · rcases den_good e ls s with hd | ⟨o', ho', -⟩
    · exact hd
    · exact absurd ho' (h o')

/-- The value of a call outcome. -/
def encFV (o : FOut) (s : S) : Except PUnit.{2} (ULift.{1} (Option WVal) × S) :=
  match o with
  | .ret r => .ok (⟨r⟩, s)
  | .trap => .error ⟨⟩

theorem encF_eq (o : FOut) (s : S) : (callTree o s : Tree (SigEv E) _) = ret (encFV o s) := by
  cases o <;> rfl

theorem encF_inj {o o' : FOut} {s : S} (h : (callTree o s : Tree (SigEv E) _) = callTree o' s) :
    o = o' := by
  cases o <;> cases o' <;> simp_all [callTree]

theorem encF_ne_diverge (o : FOut) (s : S) : (callTree o s : Tree (SigEv E) _) ≠ diverge := by
  cases o <;> exact ret_ne_diverge _

theorem blockExit_none (out : Out (Option WVal)) : ∃ out', BlockExit none out out' := by
  cases out with
  | ok ls r => exact ⟨_, .ok (by simp [BlockOk])⟩
  | brk l ls r =>
    cases l with
    | zero => exact ⟨_, .brk0 (by simp [BlockOk])⟩
    | succ l => exact ⟨_, .brk⟩
  | ret r => exact ⟨_, .ret⟩
  | trap => exact ⟨_, .trap⟩

theorem seq_den {ls : List WVal} {es : List Expr} {o : Out (Option WVal)} (h : Seq ls none es o)
    (s : S) : run' (denSeq es ls none : M E S OutE) s = outTree o s := by
  rcases denSeq_good es ls none s with hd | ⟨o', ho', h'⟩
  · obtain ⟨o'', hx⟩ := blockExit_none o
    have := exec_den (E := E) (Exec.block h hx) s
    simp only [den] at this
    rw [run_bind_diverge hd] at this
    exact absurd this.symm (encT_ne_diverge _ _)
  · rw [Seq.det h ho']; exact h'

theorem funcK_run {res : Option Silmaril.Wasm.IntType} {out : Out (Option WVal)} {s : S} :
    (∃ o, funcExit res out = some o ∧ run' (funcK res out : M E S _) s = callTree o s) ∨
      (funcExit res out = none ∧ run' (funcK res out : M E S _) s = diverge) := by
  cases h : funcExit res out with
  | none => exact .inr ⟨rfl, by simp only [funcK, h]; rfl⟩
  | some o =>
    refine .inl ⟨o, rfl, ?_⟩
    cases o with
    | ret r => simp only [funcK, h]; rfl
    | trap => simp only [funcK, h]; exact run_trap s

theorem denFunc_good (f : FragFunc) (args : List WVal) (s : S) :
    run' (denFunc f ⟨args⟩ : M E S _) s = diverge ∨
      ∃ o, f.Run args o ∧ run' (denFunc f ⟨args⟩ : M E S _) s = callTree o s := by
  by_cases ht : args.map WVal.type = f.params
  · simp only [denFunc, ht, ↓reduceIte]
    rcases denSeq_good f.body (f.initLocals args) none s with hd | ⟨out, hseq, h⟩
    · exact .inl (run_bind_diverge hd)
    · cases out with
      | trap =>
        refine .inr ⟨.trap, ⟨ht, _, hseq, rfl⟩, run_bind_error h⟩
      | _ =>
        rw [run_bind_ok h]
        rcases funcK_run (E := E) (S := S) (res := f.result) (s := s) with ⟨o, he, hr⟩ | ⟨-, hr⟩
        · exact .inr ⟨o, ⟨ht, _, hseq, he⟩, hr⟩
        · exact .inl hr
  · simp only [denFunc, ht, ↓reduceIte]
    exact .inl rfl

theorem run_denFunc_of_run {f : FragFunc} {args : List WVal} {o : FOut} (h : f.Run args o)
    (s : S) : run' (denFunc f ⟨args⟩ : M E S _) s = callTree o s := by
  rcases denFunc_good (E := E) f args s with hd | ⟨o', ho', h'⟩
  · obtain ⟨ht, out, hseq, he⟩ := h
    simp only [denFunc, ht, ↓reduceIte] at hd
    have hs := seq_den (E := E) hseq s
    cases out with
    | trap => rw [run_bind_error hs] at hd; exact absurd hd (ret_ne_diverge _)
    | _ =>
      rw [run_bind_ok hs] at hd
      rcases funcK_run (E := E) (S := S) (res := f.result) (s := s) with ⟨o₁, he₁, hr⟩ | ⟨he₁, -⟩
      · exact absurd (hr.symm.trans hd) (encF_ne_diverge _ _)
      · rw [he] at he₁; cases he₁
  · rw [FragFunc.Run.det h ho']; exact h'

/-- The abstract body of a fragment function is exactly its runs: each run
outcome is computed, and it diverges exactly when there is no run. -/
theorem denFunc_exact (f : FragFunc) (args : List WVal) (s : S) :
    (∀ o, f.Run args o ↔ run' (denFunc f ⟨args⟩ : M E S _) s = callTree o s) ∧
      (run' (denFunc f ⟨args⟩ : M E S _) s = diverge ↔ ∀ o, ¬ f.Run args o) := by
  refine ⟨fun o => ⟨fun h => run_denFunc_of_run h s, fun h => ?_⟩, ⟨fun h o ho => ?_, fun h => ?_⟩⟩
  · rcases denFunc_good (E := E) f args s with hd | ⟨o', ho', h'⟩
    · exact absurd (h.symm.trans hd) (encF_ne_diverge o s)
    · rw [encF_inj (h.symm.trans h')]; exact ho'
  · exact encF_ne_diverge o s ((run_denFunc_of_run ho s).symm.trans h)
  · rcases denFunc_good (E := E) f args s with hd | ⟨o', ho', -⟩
    · exact hd
    · exact absurd ho' (h o')

theorem toAFun_denFunc (f : FragFunc) (args : List WVal) (s : S) :
    toAFun (denFunc f : Hom E S PUnit.{2} _ _) s ⟨args⟩ =
      {x | (∃ o, f.Run args o ∧ x = ([], foutEnd o s)) ∨ (x = ([], .div) ∧ ∀ o, ¬ f.Run args o)} := by
  rcases denFunc_good (E := E) f args s with hd | ⟨o, ho, h⟩
  · have hno := (denFunc_exact (E := E) f args s).2.1 hd
    rw [toAFun_of_run_diverge hd]
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro rfl; exact .inr ⟨rfl, hno⟩
    · rintro (⟨o, ho, -⟩ | ⟨rfl, -⟩)
      · exact absurd ho (hno o)
      · rfl
  · have hv := h.trans (encF_eq o s)
    rw [toAFun_of_run_ret hv]
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro rfl
      exact .inl ⟨o, ho, by cases o <;> rfl⟩
    · rintro (⟨o', ho', rfl⟩ | ⟨-, hno⟩)
      · rw [FragFunc.Run.det ho' ho]; cases o <;> rfl
      · exact absurd ho (hno o)

/-! ## Faithfulness -/

theorem bodyM_ext {X : Type 1} {x y : M E S X} (h : ∀ s, run' x s = run' y s) : x = y := by
  funext s; exact ExceptT.ext (h s)

/-- Two fragment functions have equal abstract bodies exactly when they have
the same runs. -/
theorem denFunc_eq_iff [Nonempty S] (f g : FragFunc) :
    (denFunc f : Hom E S PUnit.{2} _ _) = denFunc g ↔ ∀ args o, f.Run args o ↔ g.Run args o := by
  constructor
  · intro h args o
    obtain ⟨s⟩ := (inferInstance : Nonempty S)
    have hr : run' (denFunc f ⟨args⟩ : M E S _) s = run' (denFunc g ⟨args⟩ : M E S _) s := by
      rw [h]
    rw [(denFunc_exact (E := E) f args s).1 o, (denFunc_exact (E := E) g args s).1 o, hr]
  · intro h
    funext args
    refine bodyM_ext fun s => ?_
    rcases denFunc_good (E := E) f args.down s with hd | ⟨o, ho, h₁⟩
    · have hno := (denFunc_exact (E := E) f args.down s).2.1 hd
      have hno' : ∀ o, ¬ g.Run args.down o := fun o ho => hno o ((h _ _).2 ho)
      exact hd.trans ((denFunc_exact (E := E) g args.down s).2.2 hno').symm
    · exact h₁.trans (run_denFunc_of_run ((h _ _).1 ho) s).symm

end Silmaril.Proofs.Wasm.Abstract.FragBody
