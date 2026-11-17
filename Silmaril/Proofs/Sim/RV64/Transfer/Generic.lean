module

public import Silmaril.Sim.RV64.Transfer.Defs
public import Silmaril.Sim.RV64.Sym.Thms
public import Silmaril.Wasm.Logic.Core.Thms
public import Silmaril.Wasm.Logic.VCTotal.Thms

/-!
# The generic transfer: Wasm problem + translation validation ⇒ RV64 problem

* `code_of_codeAt`: `CodeAt` makes `codeAt` fetchable;
* **`fnISA_of_tree`**: if the symbolic executor yields `T` on the words and `Post` holds of
  `T.eval σ` for every `σ`, the RV64 problem `FnISA` holds (via `extSym_sound`);
* **`fnISA_of_wasm`**: the same with `Post` obtained from the Wasm side: a run of the
  instantiated function on the parameter values satisfying `Post` (the Wasm problem), and
  **translation validation**: every run returns `T.eval σ`.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Sim.RV64.Transfer

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.RiscV.Ext
open Silmaril.Sim.RV64 Silmaril.Sim.RV64.Sym

theorem code_of_codeAt {m : MState} {entry : Nat} {ws : List (BitVec 32)}
    (hc : CodeAt m entry ws) (hlen : entry + 4 * ws.length < 2 ^ 64) :
    ∀ p w, codeAt entry ws p = some w → fetch m.memory p = some w := by
  intro p w h
  simp only [codeAt] at h
  split at h
  next hp =>
    obtain ⟨hk, hw⟩ := List.getElem?_eq_some_iff.mp h
    have := hc _ hk
    have hpe : BitVec.ofNat 64 (entry + 4 * ((p.toNat - entry) / 4)) = p := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    rw [hpe, hw] at this
    exact this
  next => cases h

/-- **The RV64 problem from the symbolic tree.** -/
theorem fnISA_of_tree {entry : Nat} {ws : List (BitVec 32)} {params : List Reg}
    {Post : List W64 → W64 → Prop} {n : Nat} {T : Tree}
    (hT : extSym (codeAt entry ws) n (BitVec.ofNat 64 entry) regs0 = some T)
    (hlen : entry + 4 * ws.length < 2 ^ 64)
    (hP : ∀ σ : Reg → W64, (σ 0#5 = 0) → Post (params.map σ) (T.eval σ)) :
    FnISA entry ws params Post := by
  intro m hpc hc hra
  obtain ⟨k, m', hrun, h1, h2, h3⟩ := extSym_sound (codeAt entry ws) m.memory
    (code_of_codeAt hc hlen) (fun r => m.core.read r) hra n _ regs0 T m hT rfl hpc
    (regs0_eval m.core)
  refine ⟨k, m', hrun, h1, h3, ?_⟩
  rw [h2]
  exact hP _ (by simp)

variable {P : Profile} {host : HostSemantics Nat}

/-- **The RV64 problem from the Wasm problem**, through translation validation. -/
theorem fnISA_of_wasm {entry : Nat} {ws : List (BitVec 32)} {params : List Reg}
    {Post : List W64 → W64 → Prop} {n : Nat} {T : Tree}
    (hT : extSym (codeAt entry ws) n (BitVec.ofNat 64 entry) regs0 = some T)
    (hlen : entry + 4 * ws.length < 2 ^ 64) (s₀ : Store Nat) (a : Nat)
    (hspec : ∀ σ : Reg → W64, ∃ s' f' res,
      Steps P host (invoke s₀ a (params.map fun r => .i64 (σ r))) ⟨s', f', vals res⟩ ∧
      ∃ x, res = [.i64 x] ∧ Post (params.map σ) x)
    (htv : ∀ (σ : Reg → W64) s' f' res,
      Steps P host (invoke s₀ a (params.map fun r => .i64 (σ r))) ⟨s', f', vals res⟩ →
      res = [.i64 (T.eval σ)]) :
    FnISA entry ws params Post := by
  refine fnISA_of_tree hT hlen fun σ _ => ?_
  obtain ⟨s', f', res, hs, x, rfl, hp⟩ := hspec σ
  have := htv σ s' f' _ hs
  have hx := congrArg (fun l : List Val => match l with
    | [.num ⟨.int .i64, x⟩] => (x : BitVec 64) | _ => 0) this
  simp only [Val.i64] at hx
  rw [← hx]; exact hp

section Wasm

variable {s₀ : Store Nat} {a : Nat} {fi : FuncInst Nat} {func : Func}
  {ps rs : Silmaril.Wasm.Validation.Ty (.list .val)} {params : List Reg} {T : Tree}

/-- The body condition for translation validation: from any store and parameter values `σ`,
the body returns `T.eval σ`. -/
def BodyTV (func : Func) (params : List Reg) (T : Tree) : Prop :=
  ∀ {H : Type} (σ : Reg → W64) (s : Store H) (m : ModuleInst) (Q : Silmaril.Wasm.Logic.Core.Post H),
    (∀ f, Q s f (.ret [.i64 (T.eval σ)])) →
    Silmaril.Wasm.Logic.VC.wpc (fun _ _ _ _ => True) 0 func.body Q s
      (Frame.forCall m (params.map fun r => .i64 (σ r)) func.locals) []

/-- **Translation validation** from the body condition: every run returns `T.eval σ`. -/
theorem tv_of_body (hf : s₀.funcs[a]? = some fi) (hcode : fi.code = .wasm func)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = params.length) (hrs : rs.length = 1)
    (hl : Silmaril.Wasm.Logic.VC.loops func.body = 0) (hb : BodyTV func params T)
    (σ : Reg → W64) {s' : Store Nat} {f' : Frame} {res : List Val}
    (hs : Steps P host (invoke s₀ a (params.map fun r => .i64 (σ r))) ⟨s', f', vals res⟩) :
    res = [.i64 (T.eval σ)] := by
  let S : Silmaril.Wasm.Logic.Hoare.FSpec Nat :=
    { pre := fun s args => s.funcs[a]? = some fi ∧ args = params.map fun r => .i64 (σ r)
      post := fun _ _ _ o => o = .normal [.i64 (T.eval σ)] }
  have hT : Silmaril.Wasm.Logic.Hoare.TFSpecAt P host a S := by
    refine Silmaril.Wasm.Logic.VC.TFSpecAt.of_fnPost (fun _ _ h => h.1) hcode he
      (fun _ _ h => by rw [h.2, hps, List.length_map]) ?_
    rintro s args ⟨-, rfl⟩
    rw [hrs]
    have := Silmaril.Wasm.Logic.VC.wpc_sound_total (P := P) (host := host) (fun _ _ _ _ => True) 0
      func.body hl (Silmaril.Wasm.Logic.VC.fnPost 1 (S.post s (params.map fun r => .i64 (σ r)))) s
      (Frame.forCall fi.module (params.map fun r => .i64 (σ r)) func.locals) []
      (hb σ s fi.module _ fun _ => by simp [Silmaril.Wasm.Logic.VC.fnPost, S])
    simpa [vals] using this
  have := Silmaril.Wasm.Logic.Hoare.FSpecValid.invoke_vals hT.valid
    (show S.pre s₀ _ from ⟨hf, rfl⟩) hs
  simpa [S] using this

/-- A run with the specified result from the Wasm problem (body-level `WP` in the store `s₀`
and the module of function `a`, as in the `Silmaril.WasmSpec.Rv64*` entries). -/
theorem run_of_wp {Post : List W64 → W64 → Prop} (hf : s₀.funcs[a]? = some fi)
    (hcode : fi.code = .wasm func)
    (he : Silmaril.Wasm.Validation.Expand fi.type (.func ps rs))
    (hps : ps.length = params.length) (hrs : rs.length = 1)
    (hW : ∀ σ : Reg → W64,
      Silmaril.Wasm.Logic.Core.WP P host s₀ (Frame.forCall fi.module (params.map fun r => .i64 (σ r))
        func.locals) (expression func.body) (Silmaril.Wasm.Logic.Core.funcPost P host 1 fun s' r =>
          s' = s₀ ∧ ∃ x, r = [.i64 x] ∧ Post (params.map σ) x)) (σ : Reg → W64) :
    ∃ s' f' res, Steps P host (invoke s₀ a (params.map fun r => .i64 (σ r))) ⟨s', f', vals res⟩ ∧
      ∃ x, res = [.i64 x] ∧ Post (params.map σ) x := by
  obtain ⟨s', res, hs, -, hp⟩ := Silmaril.Wasm.Logic.Core.funcSpec_invoke_of_body (P := P) (host := host)
    (a := a) (Pre := fun s args => s = s₀ ∧ args = params.map fun r => .i64 (σ r))
    (Post := fun s _ s' res => s' = s ∧ ∃ x, res = [.i64 x] ∧ Post (params.map σ) x)
    (fun _ _ h => by rw [h.1]; exact hf) hcode he (fun _ _ h => by rw [h.2, hps, List.length_map])
    (fun s args h => by obtain ⟨rfl, rfl⟩ := h; rw [hrs]; exact hW σ) ⟨rfl, rfl⟩
  exact ⟨s', {}, res, hs, hp⟩

/-- **A Wasm solution from the body condition**: the body returns `T.eval σ`, so it has a run
satisfying any postcondition `T.eval σ` satisfies. -/
theorem wp_of_body (hl : Silmaril.Wasm.Logic.VC.loops func.body = 0) (hb : BodyTV func params T)
    {H : Type} {P : Profile} {host : HostSemantics H}
    (σ : Reg → W64) (s : Store H) (m : ModuleInst)
    (K : Store H → List Val → Prop) (hK : K s [.i64 (T.eval σ)]) :
    Silmaril.Wasm.Logic.Core.WP P host s (Frame.forCall m (params.map fun r => .i64 (σ r)) func.locals)
      (expression func.body) (Silmaril.Wasm.Logic.Core.funcPost P host 1 K) := by
  refine Silmaril.Wasm.Logic.VC.wp_of_twp (fun _ _ => ⟨id, fun _ => id⟩) ?_
  have := Silmaril.Wasm.Logic.VC.wpc_sound_total (P := P) (host := host) _ 0 func.body hl
    (Silmaril.Wasm.Logic.Core.funcPost P host 1 K) s _ [] (hb σ s m _ fun _ => ⟨[], _, rfl, rfl, hK⟩)
  simpa [vals] using this

end Wasm

/-- The store after instantiating a module against no imports. -/
def instStore (mod : Module) : Store Nat :=
  match instantiateOnce? (Silmaril.Wasm.Game.importStore []) mod [] with
  | some (s, _, _) => s
  | none => {}

/-- Close a translation-validation body condition (`BodyTV`): evaluate the tree and the body's
`wpc`, then match every return against the tree's value. -/
syntax "rv_tv" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| rv_tv [$ls,*]) => `(tactic| (
      intro _ σ s m Q hQ
      simp only [Silmaril.Sim.RV64.Sym.Tree.eval, Silmaril.Sim.RV64.Sym.E.eval,
        Silmaril.Sim.RV64.Sym.Bin.eval, Silmaril.RiscV.Ext.BranchOp.eval, List.map_cons,
        List.map_nil, Silmaril.Wasm.Execution.Core.Val.i64, $ls,*] at hQ ⊢
      simp [Silmaril.Wasm.Logic.VC.wpc, Silmaril.Wasm.Logic.VC.ctl, Silmaril.Wasm.Logic.VC.enterVC,
        Silmaril.Wasm.Logic.VC.labelQ, Silmaril.Wasm.Logic.VC.popI32, Silmaril.Wasm.Logic.Core.exec1,
        Silmaril.Wasm.Logic.Core.popInt, Silmaril.Wasm.Logic.Core.popV, Silmaril.Wasm.Logic.Core.localVal?,
        Silmaril.Wasm.Execution.Core.Frame.local?, Silmaril.Wasm.Execution.Core.Frame.setLocal,
        Silmaril.Wasm.Execution.Core.Frame.forCall, Silmaril.Wasm.Execution.Core.ModuleInst.blockType?,
        Silmaril.Wasm.Idx.toNat, Silmaril.Wasm.Execution.Core.Val.i64,
        Silmaril.Wasm.Execution.Core.Val.i32, Silmaril.Wasm.Logic.VC.intRelOp_i64_ltS,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_geS, Silmaril.Wasm.Logic.VC.intRelOp_i64_gtS,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_leS, Silmaril.Wasm.Logic.VC.intRelOp_i64_ltU,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_geU, Silmaril.Wasm.Logic.VC.intRelOp_i64_eq,
        Silmaril.Wasm.Logic.VC.intRelOp_i64_ne, Silmaril.Wasm.Logic.VC.defaultVal_i64,
        Silmaril.Wasm.Numerics.bool32, BitVec.slt, $ls,*]
      repeat' (first | apply And.intro | intro)
      all_goals
        convert hQ _ using 5
        all_goals (try simp only [Silmaril.Wasm.Execution.Core.NumVal.mk.injEq, heq_eq_eq, true_and, BitVec.add_zero, BitVec.slt,
          decide_eq_true_eq])
        all_goals (try split_ifs)
        all_goals (try (first | rfl | (exfalso; omega) | (apply BitVec.eq_of_toInt_eq; omega) |
          simp_all [BitVec.slt]))))

end Silmaril.Sim.RV64.Transfer
