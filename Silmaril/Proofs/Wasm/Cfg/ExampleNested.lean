module

public import Silmaril.Wasm.Cfg.ExampleNested.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Proofs.Wasm.Cfg.Region
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

/-!
# Validated typed nested fixtures for the block-CFG machines (proofs)
-/

namespace Silmaril.Wasm.Cfg.Proofs.ExampleNested

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Binaryen Silmaril.Wasm.Cfg.ExampleNested
open Silmaril.Wasm.Abstract (EvalLXPS SCall)

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem nestMod_valid : (Validation.validate? nestMod).isSome = true := by decide +kernel

/-! ## Straight-line helpers -/

theorem val_i32 (k : BitVec 32) : (Admin.plain (.intConst .i32 k)).val? = some (.i32 k) := rfl

/-- A flat instruction, natively. -/
theorem ev_op {s s₂ : Store H} {f f₂ : Frame} {stk stk₂ : List Val} {i : Instr} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × Abstract.CallXP.POut} (hi : ∀ x, i ≠ .call x)
    (h : evalFlat s f stk i = some (s₂, f₂, .normal stk₂)) (hk : EvalLXPS s₂ f₂ stk₂ es l r) :
    EvalLXPS s f stk (.op i [] :: es) l r := by
  simpa using EvalLXPS.opOk (l₁ := []) hi .nil h hk

/-- A flat instruction ending the code abruptly, natively. -/
theorem ev_stop {s s₂ : Store H} {f f₂ : Frame} {stk : List Val} {i : Instr} {es : List BExpr}
    {fl : Flow} (hi : ∀ x, i ≠ .call x) (h : evalFlat s f stk i = some (s₂, f₂, fl))
    (hfl : ¬ fl.IsNormal) : EvalLXPS (H := H) s f stk (.op i [] :: es) [] (s₂, f₂, .flow fl) :=
  EvalLXPS.opStop hi .nil h hfl

/-- A simple instruction by one Core step, in `RunC`. -/
theorem run_step {s s' : Store H} {f f₁ f' : Frame} {vs us ws : List Val} {i : Instr}
    {code : List Admin} {o : Region.Out} (hi : SingleThreaded.Det.famOf (.plain i) ≠ .control)
    (h : Step P host ⟨s, f, vals us ++ [.plain i]⟩ ⟨s, f₁, vals ws⟩)
    (hk : RunC P host C s f₁ (vs ++ ws) code s' f' o) :
    RunC P host C s f (vs ++ us) (.plain i :: code) s' f' o := by
  have := Proofs.Region.step_in (P := P) (host := host) vs [] h
  exact .simple (vs₁ := vs ++ ws) hi (.single (by simpa [vals_append] using this)) hk

/-- `local.get x`, in `RunC`. -/
theorem run_localGet {s s' : Store H} {f f' : Frame} {vs : List Val} {x : LocalIdx} {v : Val}
    {code : List Admin} {o : Region.Out} (h : f.local? x = some (some v))
    (hk : RunC P host C s f (vs ++ [v]) code s' f' o) :
    RunC P host C s f vs (.plain (.localGet x) :: code) s' f' o := by
  simpa using run_step (vs := vs) (us := []) (ws := [v]) (by simp [SingleThreaded.Det.famOf])
    (Step.variable (VariableStep.localGet h)) hk

/-- `local.set x`, in `RunC`. -/
theorem run_localSet {s s' : Store H} {f f' : Frame} {vs : List Val} {x : LocalIdx} {v : Val}
    {code : List Admin} {o : Region.Out} (hx : x.toNat < f.locals.length)
    (hk : RunC P host C s (f.setLocal x v) vs code s' f' o) :
    RunC P host C s f (vs ++ [v]) (.plain (.localSet x) :: code) s' f' o := by
  simpa using run_step (vs := vs) (us := [v]) (ws := []) (by simp [SingleThreaded.Det.famOf])
    (Step.variable (VariableStep.localSet hx)) (by simpa using hk)

/-- `i32.eqz`, in `RunC`. -/
theorem run_eqz {s s' : Store H} {f f' : Frame} {vs : List Val} {k : BitVec 32}
    {code : List Admin} {o : Region.Out}
    (hk : RunC P host C s f (vs ++ [.i32 (Numerics.intTestOp .i32 .eqz k)]) code s' f' o) :
    RunC P host C s f (vs ++ [.i32 k]) (.plain (.intTestOp .i32 .eqz) :: code) s' f' o :=
  run_step (vs := vs) (us := [.i32 k]) (by simp [SingleThreaded.Det.famOf])
    (Step.numeric (NumericStep.intTestOp (t := .i32) (op := .eqz) (x := k))) hk

/-- `i32.add`, in `RunC`. -/
theorem run_add {s s' : Store H} {f f' : Frame} {vs : List Val} {a b : BitVec 32}
    {code : List Admin} {o : Region.Out}
    (hk : RunC P host C s f (vs ++ [.i32 (a + b)]) code s' f' o) :
    RunC P host C s f (vs ++ [.i32 a, .i32 b]) (.plain (.intBinOp .i32 .add) :: code) s' f' o :=
  run_step (vs := vs) (us := [.i32 a, .i32 b]) (by simp [SingleThreaded.Det.famOf])
    (Step.numeric (NumericStep.intBinOp (t := .i32) (op := .add) (x := a) (y := b) rfl)) hk

/-- A structured instruction other than `if` enters its arm on no parameters. -/
theorem cond_plain {i : Instr} {ws : List Val} (hi : ∀ bt t e, i ≠ .if_ bt t e) :
    CondArm i ws 0 ws [] := by
  simpa using CondArm.plain (i := i) (ws := ws) (us := []) hi

/-! ## `bodyNest` -/

/-- The `block`'s frame: arity `1`, the outer value `9`. -/
abbrev frB : LFrame := ⟨1, [.i32 9], false, false, [], .value .i32⟩
/-- The `loop`'s frame. -/
abbrev frL : LFrame := loopFrame
/-- The `if`'s frame. -/
abbrev frI : LFrame := ⟨0, [], false, false, [], .empty⟩

/-- **The logged machine exits `bodyNest` with `9, 42`.** -/
theorem nest_logged (s : Store H) (f : Frame) :
    MRunL bodyNest (initial bodyNest s f) [] ⟨.exit, [.i32 9, .i32 42], [], s, f⟩ := by
  have h₁ : MStepL bodyNest (initial bodyNest s f) [] ⟨.block ⟨[(0, 0)], 0⟩, [], [frB], s, f⟩ :=
    MStepL.enter (b := ⟨[], 0⟩) (sg := ⟨[.intConst .i32 9], some (.block (.value .i32) nestBlock)⟩)
      (a := 0) (V := [.i32 9]) (V' := [.i32 9]) rfl rfl rfl .block
      (ev_op (fun _ => nofun) rfl .nil) (.plain (fun _ _ _ => nofun)) rfl rfl
  have h₂ : MStepL bodyNest ⟨.block ⟨[(0, 0)], 0⟩, [], [frB], s, f⟩ []
      ⟨.block ⟨[(0, 0), (0, 0)], 0⟩, [], [frL, frB], s, f⟩ :=
    MStepL.enter (sg := ⟨[], some (.loop .empty nestLoop)⟩) (a := 0) (V := []) (V' := [])
      rfl rfl rfl .loop .nil (.plain (fun _ _ _ => nofun)) rfl rfl
  have h₃ : MStepL bodyNest ⟨.block ⟨[(0, 0), (0, 0)], 0⟩, [], [frL, frB], s, f⟩ []
      ⟨.block ⟨[(0, 0), (0, 0), (0, 0)], 0⟩, [], [frI, frL, frB], s, f⟩ :=
    MStepL.enter (sg := ⟨[.intConst .i32 1], some (.if_ .empty nestThen [])⟩) (a := 0)
      (V := [.i32 1]) (V' := []) rfl rfl rfl .if_ (ev_op (fun _ => nofun) rfl .nil)
      (ArmSel.cond (b := true) rfl) rfl rfl
  have h₄ : MStepL bodyNest ⟨.block ⟨[(0, 0), (0, 0), (0, 0)], 0⟩, [], [frI, frL, frB], s, f⟩ []
      ⟨.exit, [.i32 9, .i32 42], [], s, f⟩ :=
    MStepL.run (sg := ⟨[.intConst .i32 42], some (.br l2)⟩) rfl
      (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk)
      (ev_op (fun _ => nofun) rfl (ev_stop (fun _ => nofun) rfl (by simp [Flow.IsNormal])))
      (DispL.br (k := 2) (L := frB) rfl rfl)
  simpa using MRunL.step h₁ (MRunL.step h₂ (MRunL.step h₃ (MRunL.step h₄ (.refl _))))

/-- **The Core machine exits `bodyNest` with `9, 42`.** -/
theorem nest_core (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyNest) (initial bodyNest s f)
      ⟨.exit, [.i32 9, .i32 42], [], s, f⟩ := by
  have h₁ : MStepC P host C bodyNest (initial bodyNest s f)
      ⟨.block ⟨[(0, 0)], 0⟩, [], [frB], s, f⟩ :=
    MStepC.enter (b := ⟨[], 0⟩) (sg := ⟨[.intConst .i32 9], some (.block (.value .i32) nestBlock)⟩)
      (a := 0) (stk₁ := [.i32 9]) (ws := [.i32 9]) (us := []) rfl rfl rfl .block
      (.val (val_i32 9) .nil) (cond_plain (fun _ _ _ => nofun)) rfl rfl
  have h₂ : MStepC P host C bodyNest ⟨.block ⟨[(0, 0)], 0⟩, [], [frB], s, f⟩
      ⟨.block ⟨[(0, 0), (0, 0)], 0⟩, [], [frL, frB], s, f⟩ :=
    MStepC.enter (sg := ⟨[], some (.loop .empty nestLoop)⟩) (a := 0) (stk₁ := []) (ws := [])
      (us := []) rfl rfl rfl .loop .nil (cond_plain (fun _ _ _ => nofun)) rfl rfl
  have h₃ : MStepC P host C bodyNest ⟨.block ⟨[(0, 0), (0, 0)], 0⟩, [], [frL, frB], s, f⟩
      ⟨.block ⟨[(0, 0), (0, 0), (0, 0)], 0⟩, [], [frI, frL, frB], s, f⟩ :=
    MStepC.enter (sg := ⟨[.intConst .i32 1], some (.if_ .empty nestThen [])⟩) (a := 0)
      (stk₁ := [.i32 1]) (ws := []) (us := []) rfl rfl rfl .if_ (.val (val_i32 1) .nil)
      (CondArm.ifTrue (ws := []) (us := []) (k := 1) (by decide)) rfl rfl
  have h₄ : MStepC P host C bodyNest
      ⟨.block ⟨[(0, 0), (0, 0), (0, 0)], 0⟩, [], [frI, frL, frB], s, f⟩
      ⟨.exit, [.i32 9, .i32 42], [], s, f⟩ :=
    MStepC.br (sg := ⟨[.intConst .i32 42], some (.br l2)⟩) (stk₁ := [.i32 42]) (L := frB) rfl rfl
      (.val (val_i32 42) .nil) rfl (by decide) nofun
  exact .head h₁ (.head h₂ (.head h₃ (.single h₄)))

/-! ## `bodyLoops` -/

/-- The inner loop's segment: its straight-line body and the `br_if 1`. -/
abbrev sgInner : Segment := ⟨loopsInner.dropLast, some (.brIf l1)⟩

theorem x0_lt (k : BitVec 32) (mi : ModuleInst) : x0.toNat < (frameK k mi).locals.length :=
  Nat.zero_lt_one

/-- The native run of the inner loop's code on the counter `0`: the branch to the outer loop,
with the counter `1`. -/
theorem loops_ev0 (s : Store H) (mi : ModuleInst) :
    EvalLXPS s (frameK 0 mi) [] (liftInstrs (MachineL.codeOf sgInner)) []
      (s, frameK 1 mi, .flow (.brk 1 [])) :=
  ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl
    (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl
      (ev_stop (fun _ => nofun) rfl (by simp [Flow.IsNormal])))))))

/-- The native run of the inner loop's code on the counter `1`: falling through, with the
counter `2`. -/
theorem loops_ev1 (s : Store H) (mi : ModuleInst) :
    EvalLXPS s (frameK 1 mi) [] (liftInstrs (MachineL.codeOf sgInner)) []
      (s, frameK 2 mi, .flow (.normal [])) :=
  ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl
    (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl (ev_op (fun _ => nofun) rfl
      (ev_op (fun _ => nofun) rfl .nil))))))

section Loops

variable (s : Store H) (mi : ModuleInst)

/-- The logged machine enters the outer loop. -/
theorem loopsL_outer :
    MStepL bodyLoops (initial bodyLoops s (frameK 0 mi)) [] (outerAt s 0 mi) :=
  MStepL.enter (sg := ⟨[], some (.loop .empty loopsOuter)⟩) (a := 0) (V := []) (V' := [])
    rfl rfl rfl .loop .nil (.plain (fun _ _ _ => nofun)) rfl rfl

/-- The logged machine enters the inner loop. -/
theorem loopsL_inner (k : BitVec 32) : MStepL bodyLoops (outerAt s k mi) [] (innerAt s k mi) :=
  MStepL.enter (sg := ⟨[], some (.loop .empty loopsInner)⟩) (a := 0) (V := []) (V' := [])
    rfl rfl rfl .loop .nil (.plain (fun _ _ _ => nofun)) rfl rfl

/-- **The logged machine re-enters the outer loop from the inner one** (`br_if 1` taken on the
counter `0`). -/
theorem loopsL_back : MStepL bodyLoops (innerAt s 0 mi) [] (outerAt s 1 mi) :=
  MStepL.run (sg := sgInner) rfl (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk)
    (loops_ev0 s mi) (DispL.br (k := 1) (L := loopFrame) rfl rfl)

/-- The logged machine leaves both loops (`br_if 1` not taken on the counter `1`) and exits. -/
theorem loopsL_exit :
    MRunL bodyLoops (innerAt s 1 mi) [] ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ := by
  have hF : MStepL bodyLoops (innerAt s 1 mi) [] ⟨.block ⟨[], 1⟩, [], [], s, frameK 2 mi⟩ :=
    MStepL.run (sg := sgInner) rfl (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk)
      (loops_ev1 s mi) (DispL.next rfl)
  have hE : MStepL bodyLoops ⟨.block ⟨[], 1⟩, [], [], s, frameK 2 mi⟩ []
      ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ :=
    MStepL.run (sg := ⟨[.localGet x0], none⟩) rfl (fun _ h => nomatch h)
      (ev_op (fun _ => nofun) rfl .nil) (DispL.next rfl)
  simpa using MRunL.step hF (MRunL.step hE (.refl _))

/-- **The logged run of `bodyLoops` through the outer re-entry**: to the inner loop on the
counter `0`, back to the outer loop, then to the exit with the counter `2`. -/
theorem loops_logged_via :
    MRunL bodyLoops (initial bodyLoops s (frameK 0 mi)) [] (innerAt s 0 mi) ∧
      MStepL bodyLoops (innerAt s 0 mi) [] (outerAt s 1 mi) ∧
      MRunL bodyLoops (outerAt s 1 mi) [] ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ :=
  ⟨by simpa using MRunL.step (loopsL_outer s mi) (MRunL.step (loopsL_inner s mi 0) (.refl _)),
    loopsL_back s mi, by simpa using MRunL.step (loopsL_inner s mi 1) (loopsL_exit s mi)⟩

/-- **The logged machine exits `bodyLoops` with the counter `2`**, re-entering the outer loop
from the inner one once. -/
theorem loops_logged :
    MRunL bodyLoops (initial bodyLoops s (frameK 0 mi)) []
      ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ := by
  simpa using MRunL.step (loopsL_outer s mi) (MRunL.step (loopsL_inner s mi 0)
    (MRunL.step (loopsL_back s mi) (MRunL.step (loopsL_inner s mi 1) (loopsL_exit s mi))))

end Loops

/-- The inner loop's straight-line body in Core, on the counter `k`: the condition
`eqz k` and the counter `k + 1`. -/
theorem loops_run (s : Store H) (mi : ModuleInst) (k : BitVec 32) :
    RunC P host C s (frameK k mi) [] (expression sgInner.body) s (frameK (k + 1) mi)
      (.normal ([] ++ [.i32 (Numerics.intTestOp .i32 .eqz k)])) :=
  run_localGet (vs := []) rfl (run_eqz (vs := []) (run_localGet
    (vs := [.i32 (Numerics.intTestOp .i32 .eqz k)]) rfl (.val (val_i32 1)
      (run_add (vs := [.i32 (Numerics.intTestOp .i32 .eqz k)]) (a := k) (b := 1)
        (run_localSet (vs := [.i32 (Numerics.intTestOp .i32 .eqz k)]) (x0_lt k mi) .nil)))))

section LoopsC

variable (s : Store H) (mi : ModuleInst)

/-- The Core machine enters the outer loop. -/
theorem loopsC_outer :
    MStepC P host C bodyLoops (initial bodyLoops s (frameK 0 mi)) (outerAt s 0 mi) :=
  MStepC.enter (sg := ⟨[], some (.loop .empty loopsOuter)⟩) (a := 0) (stk₁ := []) (ws := [])
    (us := []) rfl rfl rfl .loop .nil (cond_plain (fun _ _ _ => nofun)) rfl rfl

/-- The Core machine enters the inner loop. -/
theorem loopsC_inner (k : BitVec 32) :
    MStepC P host C bodyLoops (outerAt s k mi) (innerAt s k mi) :=
  MStepC.enter (sg := ⟨[], some (.loop .empty loopsInner)⟩) (a := 0) (stk₁ := []) (ws := [])
    (us := []) rfl rfl rfl .loop .nil (cond_plain (fun _ _ _ => nofun)) rfl rfl

/-- **The Core machine re-enters the outer loop from the inner one** (`br_if 1` taken on the
counter `0`). -/
theorem loopsC_back : MStepC P host C bodyLoops (innerAt s 0 mi) (outerAt s 1 mi) :=
  MStepC.brIfTaken (sg := sgInner) (stk₁ := []) (k := 1) (L := loopFrame) rfl rfl
    (loops_run s mi 0) (by decide) rfl (by decide) (fun _ => ⟨[], [], rfl, rfl⟩)

/-- The Core machine leaves both loops (`br_if 1` not taken on the counter `1`) and exits. -/
theorem loopsC_exit :
    Relation.ReflTransGen (MStepC P host C bodyLoops) (innerAt s 1 mi)
      ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ := by
  have hF : MStepC P host C bodyLoops (innerAt s 1 mi) ⟨.block ⟨[], 1⟩, [], [], s, frameK 2 mi⟩ :=
    MStepC.brIfNot (sg := sgInner) (stk₁ := []) rfl rfl (loops_run s mi 1)
  have hE : MStepC P host C bodyLoops ⟨.block ⟨[], 1⟩, [], [], s, frameK 2 mi⟩
      ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ :=
    MStepC.fall (sg := ⟨[.localGet x0], none⟩) (stk₁ := [.i32 2]) rfl rfl
      (run_localGet (vs := []) rfl .nil)
  exact .head hF (.single hE)

/-- **The Core run of `bodyLoops` through the outer re-entry.** -/
theorem loops_core_via :
    Relation.ReflTransGen (MStepC P host C bodyLoops) (initial bodyLoops s (frameK 0 mi))
        (innerAt s 0 mi) ∧
      MStepC P host C bodyLoops (innerAt s 0 mi) (outerAt s 1 mi) ∧
      Relation.ReflTransGen (MStepC P host C bodyLoops) (outerAt s 1 mi)
        ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ :=
  ⟨.head (loopsC_outer s mi) (.single (loopsC_inner s mi 0)), loopsC_back s mi,
    .head (loopsC_inner s mi 1) (loopsC_exit s mi)⟩

/-- **The Core machine exits `bodyLoops` with the counter `2`**, re-entering the outer loop
from the inner one once. -/
theorem loops_core :
    Relation.ReflTransGen (MStepC P host C bodyLoops) (initial bodyLoops s (frameK 0 mi))
      ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ :=
  .head (loopsC_outer s mi) (.head (loopsC_inner s mi 0) (.head (loopsC_back s mi)
    (.head (loopsC_inner s mi 1) (loopsC_exit s mi))))

end LoopsC

/-! ## `bodyTry` -/

/-- The exception `throw 0` allocates, with the payload `3`. -/
abbrev exn3 (ta : Nat) : ExnInst := ⟨ta, [.i32 3]⟩

/-- The outer `block`'s frame: arity `1`, the outer value `1`. -/
abbrev frB1 : LFrame := ⟨1, [.i32 1], false, false, [], .value .i32⟩
/-- The `try_table`'s frame. -/
abbrev frT : LFrame := ⟨0, [], false, true, [.catch_ t0 l0], .empty⟩

section Tag

variable {s : Store H} {f : Frame} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}
  (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
  (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 1)

include hmod hti in
theorem tag_t0 : s.tag? f t0 = some (ta, ti) := by
  have h0 : t0.toNat = 0 := rfl
  simp only [Store.tag?, h0, hmod]
  show (s.tags[ta]?.bind fun t => some (ta, t)) = _
  rw [hti]
  rfl

include hmod in
/-- The clause `catch 0 0` catches the exception, with its payload. -/
theorem catches_exn3 :
    Catches (s.addExn (exn3 ta)) f s.exns.length [.catch_ t0 l0] (some ([.i32 3], l0)) :=
  .catch_ (e := exn3 ta) (by simp [Store.addExn]) hmod

/-- Only the `try_table` frame (the second) is a handler. -/
theorem pass_frI {s' : Store H} {a : Nat} :
    ∀ (k : Nat) (L : LFrame), k < 1 → [frI, frT, frB1][k]? = some L → L.tryT = true →
      Catches s' f a L.catches none := by
  intro k L hk hL hT
  obtain rfl : k = 0 := by omega
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hL
  subst hL
  cases hT

include hmod hti hexp hts

/-- **The logged machine exits `bodyTry` with `4`**: the exception thrown in the nested block
is caught by the `try_table` and branches to the outer `block` with the payload over its outer
value. -/
theorem try_logged :
    MRunL bodyTry (initial bodyTry s f) [] ⟨.exit, [.i32 4], [], s.addExn (exn3 ta), f⟩ := by
  have h₁ : MStepL bodyTry (initial bodyTry s f) [] ⟨.block ⟨[(0, 0)], 0⟩, [], [frB1], s, f⟩ :=
    MStepL.enter (b := ⟨[], 0⟩) (sg := ⟨[.intConst .i32 1], some (.block (.value .i32) tryBlock)⟩)
      (a := 0) (V := [.i32 1]) (V' := [.i32 1]) rfl rfl rfl .block
      (ev_op (fun _ => nofun) rfl .nil) (.plain (fun _ _ _ => nofun)) rfl rfl
  have h₂ : MStepL bodyTry ⟨.block ⟨[(0, 0)], 0⟩, [], [frB1], s, f⟩ []
      ⟨.block ⟨[(0, 0), (0, 0)], 0⟩, [], [frT, frB1], s, f⟩ :=
    MStepL.enter (sg := ⟨[], some (.tryTable .empty [.catch_ t0 l0] tryBody)⟩) (a := 0) (V := [])
      (V' := []) rfl rfl rfl .tryTable .nil (.plain (fun _ _ _ => nofun)) rfl rfl
  have h₃ : MStepL bodyTry ⟨.block ⟨[(0, 0), (0, 0)], 0⟩, [], [frT, frB1], s, f⟩ []
      ⟨.block ⟨[(0, 0), (0, 0), (0, 0)], 0⟩, [], [frI, frT, frB1], s, f⟩ :=
    MStepL.enter (sg := ⟨[], some (.block .empty tryInner)⟩) (a := 0) (V := []) (V' := [])
      rfl rfl rfl .block .nil (.plain (fun _ _ _ => nofun)) rfl rfl
  have hth : EvalLXPS s f [] (liftInstrs (MachineL.codeOf ⟨[.intConst .i32 3], some (.throw t0)⟩))
      [] (s.addExn (exn3 ta), f, .flow (.throw s.exns.length)) := by
    have := EvalLXPS.throw (s := s) (f := f) (es := []) (args := []) (stk₁ := [.i32 3]) (l := [])
      (x := t0) .nil (tag_t0 hmod hti) hexp (by simp [hts])
    rw [hts] at this
    exact ev_op (i := .intConst .i32 3) (fun _ => nofun) rfl this
  have h₄ : MStepL bodyTry ⟨.block ⟨[(0, 0), (0, 0), (0, 0)], 0⟩, [], [frI, frT, frB1], s, f⟩ []
      ⟨.block ⟨[], 1⟩, [.i32 1, .i32 3], [], s.addExn (exn3 ta), f⟩ :=
    MStepL.run (sg := ⟨[.intConst .i32 3], some (.throw t0)⟩) rfl
      (fun _ h ⟨_, _, _, _, hk⟩ => by cases h; cases hk) hth
      (DispL.catch_ (j := 1) (L := frT) (L' := frB1) pass_frI rfl rfl (catches_exn3 hmod) rfl rfl)
  have h₅ : MStepL bodyTry ⟨.block ⟨[], 1⟩, [.i32 1, .i32 3], [], s.addExn (exn3 ta), f⟩ []
      ⟨.exit, [.i32 4], [], s.addExn (exn3 ta), f⟩ :=
    MStepL.run (sg := ⟨[.intBinOp .i32 .add], none⟩) rfl (fun _ h => nomatch h)
      (ev_op (fun _ => nofun) rfl .nil) (DispL.next rfl)
  simpa using MRunL.step h₁ (MRunL.step h₂ (MRunL.step h₃ (MRunL.step h₄ (MRunL.step h₅
    (.refl _)))))

/-- **The Core machine exits `bodyTry` with `4`.** -/
theorem try_core :
    Relation.ReflTransGen (MStepC P host C bodyTry) (initial bodyTry s f)
      ⟨.exit, [.i32 4], [], s.addExn (exn3 ta), f⟩ := by
  have h₁ : MStepC P host C bodyTry (initial bodyTry s f)
      ⟨.block ⟨[(0, 0)], 0⟩, [], [frB1], s, f⟩ :=
    MStepC.enter (b := ⟨[], 0⟩) (sg := ⟨[.intConst .i32 1], some (.block (.value .i32) tryBlock)⟩)
      (a := 0) (stk₁ := [.i32 1]) (ws := [.i32 1]) (us := []) rfl rfl rfl .block
      (.val (val_i32 1) .nil) (cond_plain (fun _ _ _ => nofun)) rfl rfl
  have h₂ : MStepC P host C bodyTry ⟨.block ⟨[(0, 0)], 0⟩, [], [frB1], s, f⟩
      ⟨.block ⟨[(0, 0), (0, 0)], 0⟩, [], [frT, frB1], s, f⟩ :=
    MStepC.enter (sg := ⟨[], some (.tryTable .empty [.catch_ t0 l0] tryBody)⟩) (a := 0)
      (stk₁ := []) (ws := []) (us := []) rfl rfl rfl .tryTable .nil
      (cond_plain (fun _ _ _ => nofun)) rfl rfl
  have h₃ : MStepC P host C bodyTry ⟨.block ⟨[(0, 0), (0, 0)], 0⟩, [], [frT, frB1], s, f⟩
      ⟨.block ⟨[(0, 0), (0, 0), (0, 0)], 0⟩, [], [frI, frT, frB1], s, f⟩ :=
    MStepC.enter (sg := ⟨[], some (.block .empty tryInner)⟩) (a := 0) (stk₁ := []) (ws := [])
      (us := []) rfl rfl rfl .block .nil (cond_plain (fun _ _ _ => nofun)) rfl rfl
  have hth : RunC P host C s f [.i32 3] [.plain (.throw t0)] (s.addExn (exn3 ta)) f
      (.throw s.exns.length) := by
    simpa [exn3] using RunC.throw (P := P) (host := host) (C := C) (ws := []) (vs := [.i32 3])
      (code := []) (tag_t0 hmod hti) hexp (by simp [hts])
  have h₄ : MStepC P host C bodyTry
      ⟨.block ⟨[(0, 0), (0, 0), (0, 0)], 0⟩, [], [frI, frT, frB1], s, f⟩
      ⟨.block ⟨[], 1⟩, [.i32 1, .i32 3], [], s.addExn (exn3 ta), f⟩ :=
    MStepC.catch_ (sg := ⟨[.intConst .i32 3], some (.throw t0)⟩) (stk₁ := [.i32 3]) (j := 1)
      (L := frT) (L' := frB1) rfl rfl trivial (.val (val_i32 3) .nil) hth pass_frI rfl rfl
      (catches_exn3 hmod) rfl (by decide) nofun
  have h₅ : MStepC P host C bodyTry ⟨.block ⟨[], 1⟩, [.i32 1, .i32 3], [], s.addExn (exn3 ta), f⟩
      ⟨.exit, [.i32 4], [], s.addExn (exn3 ta), f⟩ :=
    MStepC.fall (sg := ⟨[.intBinOp .i32 .add], none⟩) (stk₁ := [.i32 4]) rfl rfl
      (run_add (vs := []) (a := 1) (b := 3) .nil)
  exact .head h₁ (.head h₂ (.head h₃ (.head h₄ (.single h₅))))

end Tag

/-- **The tag hypotheses hold at the instance of `nestMod`**: tag `0` of the functions' module
is a tag of the store whose type expands to `[i32] → []`. -/
theorem nest_tag : ∃ (ta : Nat) (ti : TagInst) (ts : Validation.Ty (.list .val)),
    nestMI.tags[0]? = some ta ∧ nestStore.tags[ta]? = some ti ∧
    Validation.Expand ti.type (.func ts .nil) ∧ ts.length = 1 :=
  ⟨_, _, _, rfl, rfl, Validation.Expand.iff.2 rfl, rfl⟩

end Silmaril.Wasm.Cfg.Proofs.ExampleNested
