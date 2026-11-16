module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Runs
public import Silmaril.Games.Abstract.StratSession.Defs
public import Silmaril.Games.Abstract.Module.Thms

/-!
# The session closure projects onto the canonical closure (proofs)

`StratSession.eraseEnd` (`.ret (.inr ()) s ↦ .trap`) maps the session closure
`Shape.close wasmHOpenXPS` onto `Shape.close wasmHOpenXP`, with the same logs:

* `close_erase`: every session behaviour erases to a canonical one. Induction on the session
  closure: a session open behaviour is a canonical one (`open_toH`), a trap answer becoming a cut
  call (`LogE`), and a callee's store-keeping trap resolving the trap answer by `Shape.Subst.int`
  becomes its trap resolving the cut call by `Shape.Subst.intTrap` (`subst_toH`).
* `close_lift`: every canonical behaviour is an erased session one. Induction on the canonical
  closure: a resolution resolves every call (`subst_cases`), and then the log has no cut call,
  which no callee answers (`wasmEvFunXP_ret_len`), so it is a session behaviour (`open_full`); or
  it stops at a call whose callee traps (never diverges, `wasmEvFunXP_ne_div`), and that call is
  reached, so the session run answering it by the callee's trap is a session behaviour
  (`open_stop`), resolved by `Shape.Subst.int` against a store-keeping trap, or by
  `Shape.Subst.intTrap` against a plain one.
* `close_ne_trap`: the session closure has no plain trap.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingS

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Games.Abstract.StratSession (eraseEnd)

/-! ## Resolutions, generically -/

section Generic

universe u

variable {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod} {R : Type u}

theorem subst_of_substPre {L : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)}
    (h : Shape.SubstPre c L q) (e : End sh.S R) : Shape.Subst c L e (q, e) := by
  induction h with
  | nil => exact .nil e
  | ext _ ih => exact .ext ih
  | int hm _ ih => exact .int hm ih

theorem subst_of_pre {u : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)}
    (h : Shape.SubstPre c u q) {w : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R}
    {y : CallBeh sh.E sh.S R} (hs : Shape.Subst c w e y) :
    Shape.Subst c (u ++ w) e (q ++ y.1, y.2) := by
  induction h with
  | nil => exact hs
  | ext _ ih => exact .ext ih
  | int hm _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .int hm ih

/-- **A resolution resolves every call, or stops at a trapping or diverging callee.** -/
theorem subst_cases {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R}
    {y : CallBeh sh.E sh.S R} (h : Shape.Subst c x e y) :
    (Shape.SubstPre c x y.1 ∧ y.2 = e) ∨
    ∃ (u w : List (Call (sh.E ⊕ₛ sh.self))) (g : sh.F) (a : sh.A g) (s : sh.S)
      (ans : sh.B g × sh.S) (q c₁ : List (Call sh.E)),
      x = u ++ ⟨.inr ⟨g, (a, s)⟩, ans⟩ :: w ∧ Shape.SubstPre c u q ∧
      (((c₁, .trap) ∈ c g s a ∧ y = (q ++ c₁, .trap)) ∨
        ((c₁, .div) ∈ c g s a ∧ y = (q ++ c₁, .div))) := by
  induction h with
  | nil e => exact .inl ⟨.nil, rfl⟩
  | @ext m n rest e y _ ih =>
    rcases ih with ⟨hp, he⟩ | ⟨u, w, g, a, s, ans, q, c₁, rfl, hp, hst⟩
    · exact .inl ⟨.ext hp, he⟩
    · refine .inr ⟨⟨.inl m, n⟩ :: u, w, g, a, s, ans, ⟨m, n⟩ :: q, c₁, rfl, .ext hp, ?_⟩
      rcases hst with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
      · exact .inl ⟨hm, rfl⟩
      · exact .inr ⟨hm, rfl⟩
  | @int g₀ a₀ s₀ b₀ s₀' rest e c₀ y hm₀ _ ih =>
    rcases ih with ⟨hp, he⟩ | ⟨u, w, g, a, s, ans, q, c₁, rfl, hp, hst⟩
    · exact .inl ⟨.int hm₀ hp, he⟩
    · refine .inr ⟨⟨.inr ⟨g₀, (a₀, s₀)⟩, (b₀, s₀')⟩ :: u, w, g, a, s, ans, c₀ ++ q, c₁, rfl,
        .int hm₀ hp, ?_⟩
      rcases hst with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
      · exact .inl ⟨hm, by simp⟩
      · exact .inr ⟨hm, by simp⟩
  | @intTrap g a s ans rest e c₁ hm =>
    exact .inr ⟨[], rest, g, a, s, ans, [], c₁, rfl, .nil, .inl ⟨hm, rfl⟩⟩
  | @intDiv g a s ans rest e c₁ hm =>
    exact .inr ⟨[], rest, g, a, s, ans, [], c₁, rfl, .nil, .inr ⟨hm, rfl⟩⟩

/-- The last call of a resolved prefix returned. -/
theorem substPre_last {g : sh.F} {a : sh.A g} {s : sh.S} {b : sh.B g} {s' : sh.S} :
    ∀ {u : List (Call (sh.E ⊕ₛ sh.self))} {q : List (Call sh.E)},
      Shape.SubstPre c (u ++ [⟨.inr ⟨g, (a, s)⟩, (b, s')⟩]) q →
      ∃ c₁, (c₁, .ret b s') ∈ c g s a
  | [], _, h => by
    cases h with
    | int hm _ => exact ⟨_, hm⟩
  | ⟨.inl _, _⟩ :: _, _, h => by
    cases h with
    | ext h => exact substPre_last h
  | ⟨.inr ⟨_, (_, _)⟩, (_, _)⟩ :: _, _, h => by
    cases h with
    | int _ h => exact substPre_last h

/-- A resolution against a module with no plain trap, of an open behaviour that does not end in a
plain trap, does not end in a plain trap. -/
theorem subst_ne_trap (hc : ∀ g s a (c₁ : List (Call sh.E)), (c₁, .trap) ∉ c g s a)
    {x : List (Call (sh.E ⊕ₛ sh.self))} {e : End sh.S R} {y : CallBeh sh.E sh.S R}
    (h : Shape.Subst c x e y) (he : e ≠ .trap) : y.2 ≠ .trap := by
  induction h with
  | nil => exact he
  | ext _ ih => exact ih he
  | int _ _ ih => exact ih he
  | intTrap hm => exact absurd hm (hc _ _ _ _)
  | intDiv _ => exact nofun

end Generic

variable {H : Type}

/-! ## Erasing ends -/

@[simp] theorem eraseEnd_endOfFlowS (fl : Flow) (s : Store H) :
    eraseEnd (endOfFlowS fl s) = endOfFlow fl s := by
  cases fl <;> rfl

@[simp] theorem eraseEnd_tailAnsS (m n : Nat) (b : List Val ⊕ Nat) (s : Store H) :
    eraseEnd (tailAnsS m n (.inl b) s) = tailAns m n b s := by
  simp only [tailAnsS, tailAns]
  cases exitFlow m (CallX.tailFlow n (ansFlow b)) with
  | none => rfl
  | some fl => exact eraseEnd_endOfFlowS fl s

theorem eraseEnd_eq_ret {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})} {b : List Val ⊕ Nat}
    {s : Store H} (h : eraseEnd e = .ret b s) : e = .ret (.inl b) s := by
  rcases e with ⟨b' | _, s'⟩ | _ | _ <;> simp_all [eraseEnd]

theorem eraseEnd_eq_trap {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (h : eraseEnd e = .trap) : e = .trap ∨ ∃ s, e = .ret (.inr ()) s := by
  rcases e with ⟨b' | _, s'⟩ | _ | _ <;> simp_all [eraseEnd]

theorem endOfFlowS_ne_trap (fl : Flow) (s : Store H) : endOfFlowS fl s ≠ .trap := by
  cases fl <;> simp [endOfFlowS]

theorem tailAnsS_ne_trap (m n : Nat) (b : (List Val ⊕ Nat) ⊕ PUnit.{1}) (s : Store H) :
    tailAnsS m n b s ≠ .trap := by
  unfold tailAnsS
  split
  · split
    · exact endOfFlowS_ne_trap _ _
    · exact nofun
  · exact nofun

@[simp] theorem hToS_comp_lift : (hToS ∘ OCall.lift : OCall H → SCall H) = oToS :=
  funext hToS_lift

@[simp] theorem map_lift_hToS (l : List (OCall H)) :
    (l.map OCall.lift).map hToS = l.map oToS := by
  induction l <;> simp [*]

/-! ## Session behaviours erase to canonical ones -/

/-- A session open behaviour `(l, e)` and a canonical one `(l', e')`: the same calls with the same
answers, the end erased, except that a final trap answer may be any answer of the canonical call,
followed by anything, the session end then erasing to a trap. -/
inductive LogE : List (SCall H) → End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1}) → List (HCall H) →
    End (Store H) (List Val ⊕ Nat) → Prop where
  | nil (e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})) : LogE [] e [] (eraseEnd e)
  | ext {m : (wasmHostSig H).Op} {n : (wasmHostSig H).Ar m} {l : List (SCall H)}
      {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})} {l' : List (HCall H)}
      {e' : End (Store H) (List Val ⊕ Nat)} :
      LogE l e l' e' → LogE (⟨.inl m, n⟩ :: l) e (⟨.inl m, n⟩ :: l') e'
  | ret {y : (wasmHShape H).self.Op} {b : List Val ⊕ Nat} {s' : Store H} {l : List (SCall H)}
      {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})} {l' : List (HCall H)}
      {e' : End (Store H) (List Val ⊕ Nat)} :
      LogE l e l' e' → LogE (⟨.inr y, (.inl b, s')⟩ :: l) e (⟨.inr y, (b, s')⟩ :: l') e'
  | trap {y : (wasmHShape H).self.Op} {s₂ : Store H} {ans : (List Val ⊕ Nat) × Store H}
      {w' : List (HCall H)} {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
      {e' : End (Store H) (List Val ⊕ Nat)} (he : eraseEnd e = .trap) :
      LogE [⟨.inr y, (.inr (), s₂)⟩] e (⟨.inr y, ans⟩ :: w') e'

theorem logE_map (e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})) :
    ∀ l : List (OCall H), LogE (l.map oToS) e (l.map OCall.lift) (eraseEnd e)
  | [] => .nil e
  | ⟨.inr _, (_, _)⟩ :: l => .ret (logE_map e l)

theorem logE_trap {y : (wasmHShape H).self.Op} {s₂ : Store H} {ans : (List Val ⊕ Nat) × Store H}
    {w' : List (HCall H)} {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    {e' : End (Store H) (List Val ⊕ Nat)} (he : eraseEnd e = .trap) :
    ∀ u : List (OCall H), LogE (u.map oToS ++ [⟨.inr y, (.inr (), s₂)⟩]) e
      (u.map OCall.lift ++ ⟨.inr y, ans⟩ :: w') e'
  | [] => .trap he
  | ⟨.inr _, (_, _)⟩ :: u => .ret (logE_trap he u)

/-- **A session resolution is a canonical resolution of the related open behaviour**, against a
module whose behaviours erase to the canonical closure's. -/
theorem subst_toH {c : (wasmHShapeS H).ClosedMod}
    (hc : ∀ g s a (y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})),
      y ∈ c g s a → (y.1, eraseEnd y.2) ∈ Shape.close wasmHOpenXP g s a)
    {L : List (SCall H)} {e : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    {y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (h : Shape.Subst c L e y) :
    ∀ {L' : List (HCall H)} {e' : End (Store H) (List Val ⊕ Nat)}, LogE L e L' e' →
      Shape.Subst (Shape.close wasmHOpenXP) L' e' (y.1, eraseEnd y.2) := by
  induction h with
  | nil e =>
    intro L' e' hE
    cases hE
    exact .nil _
  | ext _ ih =>
    intro L' e' hE
    cases hE with
    | ext hE => exact .ext (ih hE)
  | @int g a s b s' rest e c₁ y hm hs ih =>
    intro L' e' hE
    cases hE with
    | ret hE => exact .int (hc _ _ _ _ hm) (ih hE)
    | @trap _ _ _ w' _ _ he =>
      cases hs
      have hm' : (c₁, End.trap) ∈ Shape.close wasmHOpenXP g s a := hc _ _ _ _ hm
      simpa [he] using Shape.Subst.intTrap (rest := w') (e := e') hm'
  | intTrap hm =>
    intro L' e' hE
    cases hE with
    | ret _ => exact .intTrap (hc _ _ _ _ hm)
    | trap _ => exact .intTrap (hc _ _ _ _ hm)
  | intDiv hm =>
    intro L' e' hE
    cases hE with
    | ret _ => exact .intDiv (hc _ _ _ _ hm)
    | trap _ => exact .intDiv (hc _ _ _ _ hm)

/-- **A session open behaviour is related to a canonical one.** -/
theorem open_toH {a : Nat} {s : Store H} {vs : List Val}
    {x : CallBeh ((wasmHShapeS H).E ⊕ₛ (wasmHShapeS H).self) (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hx : x ∈ wasmHOpenXPS a s vs) : ∃ x' ∈ wasmHOpenXP a s vs, LogE x.1 x.2 x'.1 x'.2 := by
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hf, hc, hty, hrun, hex, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, hf, hc, hty, hrun, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hf, hc, hty, hex, rfl⟩
  · rcases evalLXPS_toH hrun with ⟨l', rfl, h'⟩ | ⟨ht, u, g, args, s₁, s₂, ws, -, rfl, h'⟩
    · refine ⟨(l'.map OCall.lift, endOfFlow fl s'),
        .inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l', hf, hc, hty, h', hex, rfl⟩, ?_⟩
      simpa using logE_map (endOfFlowS fl s') l'
    · cases ht
      cases hex
      refine ⟨((u ++ [OCall.mk g args s₁ (.inl ws) s₂]).map OCall.lift, endOfFlow .trap s'),
        .inl ⟨fi, fn, ps, rs, s', f₂, .trap, .trap, _, hf, hc, hty, h', rfl, rfl⟩, ?_⟩
      rw [List.map_append]
      exact logE_trap rfl u
  · obtain ⟨l', rfl, h'⟩ := (evalLXPS_toH hrun).ok (by simp)
    rcases b with b | ⟨⟩
    · refine ⟨((l' ++ [OCall.mk a' args s₁ b s₂]).map OCall.lift, tailAns rs.length n b s₂),
        .inr (.inl ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l', hf, hc, hty, h', rfl⟩), ?_⟩
      simpa using logE_map (tailAnsS rs.length n (.inl b) s₂) (l' ++ [OCall.mk a' args s₁ b s₂])
    · refine ⟨((l' ++ [OCall.mk a' args s₁ (.inl []) s₂]).map OCall.lift,
        tailAns rs.length n (.inl []) s₂),
        .inr (.inl ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, .inl [], l', hf, hc, hty, h', rfl⟩),
        ?_⟩
      rw [List.map_append]
      exact logE_trap rfl l'
  · refine ⟨([⟨.inl (hh, s, vs), (s', r)⟩], endOfFlow fl s'),
      .inr (.inr ⟨fi, hh, ps, rs, s', r, fl, hf, hc, hty, hex, rfl⟩), ?_⟩
    simpa using LogE.ext (m := (hh, s, vs)) (n := (s', r)) (LogE.nil (endOfFlowS fl s'))

/-- **Every session behaviour erases to a canonical behaviour**, with the same log. -/
theorem close_erase {a : Nat} {s : Store H} {vs : List Val}
    {y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hy : y ∈ Shape.close wasmHOpenXPS a s vs) :
    (y.1, eraseEnd y.2) ∈ Shape.close wasmHOpenXP a s vs := by
  have key : Shape.close (wasmHOpenXPS (H := H)) ≤
      fun a s vs => {y | (y.1, eraseEnd y.2) ∈ Shape.close wasmHOpenXP a s vs} := by
    refine OrderHom.lfp_le _ ?_
    rintro a s vs y ⟨x, hx, hS⟩
    obtain ⟨x', hx', hE⟩ := open_toH hx
    show _ ∈ Shape.close wasmHOpenXP a s vs
    rw [← Shape.resolve_close]
    exact ⟨x', hx', subst_toH (fun _ _ _ _ h => h) hS hE⟩
  exact key a s vs hy

/-! ## Canonical behaviours lift to session ones -/

/-- A canonical resolved prefix is a session resolved prefix, against a module whose behaviours
are erased session behaviours. -/
theorem substPre_toS {c : (wasmHShape H).ClosedMod}
    (hc : ∀ g s a (y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)), y ∈ c g s a →
      ∃ y' ∈ Shape.close wasmHOpenXPS g s a, y'.1 = y.1 ∧ eraseEnd y'.2 = y.2)
    {L : List (HCall H)} {q : List (Call (wasmHostSig H))} (h : Shape.SubstPre c L q) :
    Shape.SubstPre (Shape.close wasmHOpenXPS) (L.map hToS) q := by
  induction h with
  | nil => exact .nil
  | ext _ ih => exact .ext ih
  | int hm _ ih =>
    obtain ⟨⟨c₁', e'⟩, hy', h1, h2⟩ := hc _ _ _ _ hm
    obtain rfl : c₁' = _ := h1
    obtain rfl := eraseEnd_eq_ret h2
    exact .int hy' ih

/-- **A canonical open behaviour is a session one**, its end erased, unless its log ends in a cut
call. -/
theorem open_full {a : Nat} {s : Store H} {vs : List Val}
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) :
    (∃ eS, (x.1.map hToS, eS) ∈ wasmHOpenXPS a s vs ∧ eraseEnd eS = x.2) ∨
    ∃ (u : List (HCall H)) (g : Nat) (args : List Val) (s₁ s₂ : Store H) (ws : List Val)
      (fi : FuncInst H) (ps rs : List Validation.CValType),
      x.1 = u ++ [⟨.inr ⟨g, (args, s₁)⟩, (.inl ws, s₂)⟩] ∧ s₁.funcs[g]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ rs.length < ws.length := by
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hf, hc, hty, hrun, hex, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, hf, hc, hty, hrun, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hf, hc, hty, hex, rfl⟩
  · rcases evalLXPh_toS hrun with h' | ⟨-, u, g, args, s₁, s₂, ws, fi', ps', rs', rfl, hc'⟩
    · refine .inl ⟨endOfFlowS fl s', ?_, by simp⟩
      rw [map_lift_hToS]
      exact .inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, _, hf, hc, hty, h', hex, rfl⟩
    · exact .inr ⟨u.map OCall.lift, g, args, s₁, s₂, ws, fi', ps', rs', by simp; rfl, hc'⟩
  · have h' := evalLXPh_toS_ok hrun (by simp)
    refine .inl ⟨tailAnsS rs.length n (.inl b) s₂, ?_, by simp⟩
    simp only [List.map_append, map_lift_hToS]
    exact .inr (.inl ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, .inl b, _, hf, hc, hty, h', rfl⟩)
  · exact .inl ⟨endOfFlowS fl s',
      .inr (.inr ⟨fi, hh, ps, rs, s', r, fl, hf, hc, hty, hex, rfl⟩), by simp⟩

/-- A call of a canonical body run's log, answered by a trap leaving `s''`, ends a session open
behaviour, trapping in `s''`. -/
theorem body_stop {a : Nat} {s : Store H} {vs : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} (hf : s.funcs[a]? = some fi) (hc : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) {l : List (OCall H)}
    {r : Store H × Frame × POut}
    (hrun : EvalLXPh s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) l r)
    {u w : List (OCall H)} {g : Nat} {args : List Val} {s₁ s₂ : Store H} {b : List Val ⊕ Nat}
    (hl : l = u ++ OCall.mk g args s₁ b s₂ :: w) (s'' : Store H) :
    (u.map oToS ++ [⟨.inr ⟨g, (args, s₁)⟩, (.inr (), s'')⟩], .ret (.inr ()) s'') ∈
      wasmHOpenXPS a s vs := by
  obtain ⟨f', h'⟩ := reachLXP_trapS (reachLXP_of_evalLXPh hrun hl) s''
  exact .inl ⟨fi, fn, ps, rs, s'', f', .trap, .trap, _, hf, hc, hty, h', rfl, rfl⟩

theorem map_lift_split {l : List (OCall H)} {u w : List (HCall H)} {g : Nat} {args : List Val}
    {s₁ : Store H} {ans : (List Val ⊕ Nat) × Store H}
    (h : l.map OCall.lift = u ++ ⟨.inr ⟨g, (args, s₁)⟩, ans⟩ :: w) :
    ∃ u₀ w₀, l = u₀ ++ OCall.mk g args s₁ ans.1 ans.2 :: w₀ ∧ u = u₀.map OCall.lift := by
  rw [List.map_eq_append_iff] at h
  obtain ⟨u₀, r₀, rfl, rfl, h2⟩ := h
  rw [List.map_eq_cons_iff] at h2
  obtain ⟨z₀, w₀, rfl, hz, -⟩ := h2
  rcases z₀ with ⟨⟨⟨⟩⟩ | ⟨g₀, a₀, s₀⟩, b₀, s₀'⟩
  cases hz
  exact ⟨u₀, w₀, rfl, rfl⟩

/-- **A canonical open behaviour stopped at a call** gives the session open behaviour whose call
is answered by a trap leaving any store `s''`. -/
theorem open_stop {a : Nat} {s : Store H} {vs : List Val}
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) {u w : List (HCall H)} {g : Nat} {args : List Val}
    {s₁ : Store H} {ans : (List Val ⊕ Nat) × Store H}
    (hxl : x.1 = u ++ ⟨.inr ⟨g, (args, s₁)⟩, ans⟩ :: w) (s'' : Store H) :
    (u.map hToS ++ [⟨.inr ⟨g, (args, s₁)⟩, (.inr (), s'')⟩], .ret (.inr ()) s'') ∈
      wasmHOpenXPS a s vs := by
  rcases hx with ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hf, hc, hty, hrun, hex, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁', s₂', f₂, a', n, args', b, l, hf, hc, hty, hrun, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hf, hc, hty, hex, rfl⟩
  · obtain ⟨u₀, w₀, rfl, rfl⟩ := map_lift_split hxl
    rw [map_lift_hToS]
    exact body_stop hf hc hty hrun rfl s''
  · obtain ⟨u₀, w₀, hl, rfl⟩ := map_lift_split hxl
    rcases List.eq_nil_or_concat w₀ with rfl | ⟨w₁, z, rfl⟩
    · obtain ⟨hlu, hz⟩ := List.append_inj' hl rfl
      subst hlu
      simp only [List.cons.injEq, and_true] at hz
      unfold OCall.mk at hz
      cases hz
      rw [map_lift_hToS]
      exact .inr (.inl ⟨fi, fn, ps, rs, s₁, s'', f₂, g, n, args, .inr (), _, hf, hc, hty,
        evalLXPh_toS_ok hrun (by simp), rfl⟩)
    · have hl' : l ++ [OCall.mk a' args' s₁' b s₂'] =
          (u₀ ++ OCall.mk g args s₁ ans.1 ans.2 :: w₁) ++ [z] := by simpa using hl
      obtain ⟨hlu, -⟩ := List.append_inj' hl' rfl
      subst hlu
      rw [map_lift_hToS]
      exact body_stop hf hc hty hrun rfl s''
  · rcases u with _ | ⟨_, u⟩
    · obtain ⟨h1, -⟩ := List.cons.inj hxl
      cases h1
    · obtain ⟨-, h2⟩ := List.cons.inj hxl
      simp at h2

/-- **Every canonical behaviour is an erased session behaviour**, with the same log. -/
theorem close_lift {a : Nat} {s : Store H} {vs : List Val}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (hy : y ∈ Shape.close wasmHOpenXP a s vs) :
    ∃ y' ∈ Shape.close wasmHOpenXPS a s vs, y'.1 = y.1 ∧ eraseEnd y'.2 = y.2 := by
  let C : (wasmHShape H).ClosedMod := fun a s vs =>
    {y | y ∈ Shape.close wasmHOpenXP a s vs ∧
      ∃ y' ∈ Shape.close wasmHOpenXPS a s vs, y'.1 = y.1 ∧ eraseEnd y'.2 = y.2}
  have key : Shape.close (wasmHOpenXP (H := H)) ≤ C := by
    refine OrderHom.lfp_le _ ?_
    rintro a s vs y ⟨x, hx, hS⟩
    have hC : ∀ g s a y, y ∈ C g s a → ∃ y' ∈ Shape.close wasmHOpenXPS g s a,
        y'.1 = y.1 ∧ eraseEnd y'.2 = y.2 := fun _ _ _ _ h => h.2
    refine ⟨?_, ?_⟩
    · show _ ∈ Shape.close wasmHOpenXP a s vs
      rw [← Shape.resolve_close]
      exact ⟨x, hx, Shape.Subst.mono (c' := Shape.close wasmHOpenXP)
        (fun _ _ _ _ h => And.left h) hS⟩
    rw [← Shape.resolve_close]
    rcases subst_cases hS with ⟨hp, he⟩ |
      ⟨u, w, g, a', s₁, ans, q, c₁, hxl, hp, ⟨hm, rfl⟩ | ⟨hm, rfl⟩⟩
    · rcases open_full hx with ⟨eS, hxS, hE⟩ |
        ⟨u, g, args, s₁, s₂, ws, fi, ps, rs, hxl, hfi, hty, hws⟩
      · exact ⟨(y.1, eS), ⟨_, hxS, subst_of_substPre (substPre_toS hC hp) eS⟩, rfl, by
          rw [hE, he]⟩
      · rw [hxl] at hp
        obtain ⟨c₁, hm⟩ := substPre_last hp
        obtain ⟨fi', ps', rs', hfi', hty', hle⟩ := wasmEvFunXP_ret_len (s := s₁) (a := g)
          (vs := args) hm.1
        obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty'.symm.trans hty))
        omega
    · obtain ⟨⟨c₁', e''⟩, hy'', h1, h2⟩ := hm.2
      obtain rfl : c₁' = c₁ := h1
      rcases eraseEnd_eq_trap h2 with rfl | ⟨s'', rfl⟩
      · refine ⟨(q ++ c₁', .trap), ⟨_, open_stop hx hxl s₁, ?_⟩, rfl, rfl⟩
        simpa using subst_of_pre (substPre_toS hC hp)
          (Shape.Subst.intTrap (rest := []) (e := (.ret (.inr ()) s₁ : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})))
            hy'')
      · refine ⟨(q ++ c₁', .ret (.inr ()) s''), ⟨_, open_stop hx hxl s'', ?_⟩, rfl, rfl⟩
        simpa using subst_of_pre (substPre_toS hC hp)
          (Shape.Subst.int hy'' (Shape.Subst.nil
            (.ret (.inr ()) s'' : End (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1}))))
    · exact absurd hm.1 wasmEvFunXP_ne_div
  exact (key a s vs hy).2

/-! ## No plain trap -/

theorem wasmHOpenXPS_ne_trap {a : Nat} {s : Store H} {vs : List Val}
    {x : CallBeh ((wasmHShapeS H).E ⊕ₛ (wasmHShapeS H).self) (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hx : x ∈ wasmHOpenXPS a s vs) : x.2 ≠ .trap := by
  rcases hx with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ |
    ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩
  · exact endOfFlowS_ne_trap _ _
  · exact tailAnsS_ne_trap _ _ _ _
  · exact endOfFlowS_ne_trap _ _

/-- **The session closure has no plain trap**: every trap keeps its store. -/
theorem close_ne_trap {a : Nat} {s : Store H} {vs : List Val}
    {c₁ : List (Call (wasmHostSig H))} : (c₁, .trap) ∉ Shape.close wasmHOpenXPS a s vs := by
  have key : Shape.close (wasmHOpenXPS (H := H)) ≤ fun _ _ _ => {y | y.2 ≠ .trap} := by
    refine OrderHom.lfp_le _ ?_
    rintro a s vs y ⟨x, hx, hS⟩
    exact subst_ne_trap (c := fun _ _ _ => {y | y.2 ≠ .trap}) (fun _ _ _ _ h => h rfl) hS
      (wasmHOpenXPS_ne_trap hx)
  exact fun h => key a s vs h rfl

end Silmaril.Proofs.Wasm.Abstract.HostClosingS
