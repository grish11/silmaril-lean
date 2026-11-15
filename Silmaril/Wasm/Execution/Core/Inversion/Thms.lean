module

public import Silmaril.Wasm.Execution.Core.Inversion.Defs
import Silmaril.Proofs.Wasm.Execution.Core.Inversion

@[expose] public section

/-! # Inversion of Core 3.0 steps

What a single `Step P host` (any profile, any host) can do from a given code. These are the
case analyses that simulation and adequacy proofs need about the actual Core 3.0 relation:

* **stuck codes**: `[TRAP]`, `(REF.EXN_ADDR a) THROW_REF`, `[BR l]`, `[RETURN]` do not step
  (they are results, or exits that only an enclosing context removes);
* **single instructions**: `unreachable` only traps; `block`/`loop` only enter their label
  (with no arguments, so the block type takes none); `call x` only resolves to `call_ref`; a
  `call_ref` of Wasm code only enters the callee's frame (after the values it does not take);
* **contexts**: a `LABEL`, `HANDLER` or `FRAME` configuration steps either inside, by the
  corresponding context rule, or by exactly one of the exit rules listed in
  `LabelExit`/`HandlerExit`/`FrameExit`. A frame's inner step does not see the outer frame,
  and its exits do not depend on it;
* **`loop (br 0)`**: it alternates between `loopBr0` and `labelBr0` only, diverges, and never
  reaches a result.

The `noHost` determinism toolkit (`SingleThreaded.Det`) gives some of these for the empty host;
these are stated for every host, since a host call can only fire on `val* (ref.func a)
call_ref` of host code.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {c : Config H}

/-! ## Stuck codes -/

theorem Step.trap_stuck : ¬ Step P host ⟨s, f, [.trap]⟩ c :=
  fun h => Proofs.Inversion.trap_stuck h rfl

theorem Step.throwing_stuck {a : Nat} : ¬ Step P host ⟨s, f, throwing a⟩ c :=
  fun h => Proofs.Inversion.throwing_stuck h rfl

theorem Step.br_stuck {l : LabelIdx} : ¬ Step P host ⟨s, f, [.plain (.br l)]⟩ c :=
  fun h => Proofs.Inversion.br_stuck h rfl

theorem Step.return_stuck : ¬ Step P host ⟨s, f, [.plain .return_]⟩ c :=
  fun h => Proofs.Inversion.return_stuck h rfl

/-- A result does not step. -/
theorem Step.result_stuck (r : Result) : ¬ Step P host ⟨s, f, r.toAdmin⟩ c := by
  cases r <;> first | exact Step.not_vals | exact Step.throwing_stuck | exact Step.trap_stuck

/-! ## Single instructions -/

theorem Step.unreachable_inv (h : Step P host ⟨s, f, [.plain .unreachable]⟩ c) :
    c = ⟨s, f, [.trap]⟩ :=
  Proofs.Inversion.unreachable_inv h rfl

theorem Step.block_inv {bt : BlockType} {body : List Instr}
    (h : Step P host ⟨s, f, [.plain (.block bt body)]⟩ c) :
    ∃ t₂, f.module.blockType? bt = some ([], t₂) ∧
      c = ⟨s, f, [.label t₂.length [] (expression body)]⟩ :=
  Proofs.Inversion.block_inv h rfl

theorem Step.loop_inv {bt : BlockType} {body : List Instr}
    (h : Step P host ⟨s, f, [.plain (.loop bt body)]⟩ c) :
    ∃ t₂, f.module.blockType? bt = some ([], t₂) ∧
      c = ⟨s, f, [.label 0 [.loop bt body] (expression body)]⟩ :=
  Proofs.Inversion.loop_inv h rfl

theorem Step.call_inv {x : FuncIdx} (h : Step P host ⟨s, f, [.plain (.call x)]⟩ c) :
    ∃ a fi, f.module.funcs[x.toNat]? = some a ∧ s.funcs[a]? = some fi ∧
      c = ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ :=
  Proofs.Inversion.call_inv h rfl

/-- `call x` only resolves to `call_ref` of the function it names. -/
theorem Step.call_inv_of {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (h : Step P host ⟨s, f, [.plain (.call x)]⟩ c) :
    c = ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ :=
  Proofs.Inversion.call_inv_of hx hf h

/-- A `call_ref` of Wasm code only enters the callee's frame: `call_ref-func` on the top
`ps.length` values, under the values below them (`ctxt-instrs`). -/
theorem Step.callRef_wasm_inv {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H}
    {code : Func} (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (h : Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c) :
    ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
      c = ⟨s, f, vals vs₁ ++ [.frame rs.length (Frame.forCall fi.module vs₂ code.locals)
        [.label rs.length [] (expression code.body)]]⟩ :=
  Proofs.Inversion.callRef_wasm_inv h hr hf hcode rfl

/-- With exactly the callee's arguments, the step is the `call_ref-func` rule. -/
theorem Step.callRef_wasm_inv_exact {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H}
    {code : Func} {ps rs : Ty (.list .val)} (hr : r.IsCallRef) (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (h : Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c) :
    c = ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]]⟩ :=
  Proofs.Inversion.callRef_wasm_inv_exact hr hf hcode he hn h

/-! ## Contexts -/

/-- A label steps inside (`ctxt-label`) or by an exit rule. -/
theorem Step.label_inv {n : Nat} {cont : List Instr} {is : List Admin}
    (h : Step P host ⟨s, f, [.label n cont is]⟩ c) :
    (∃ s' f' is', Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩ ∧ c = ⟨s', f', [.label n cont is']⟩) ∨
      ∃ out, LabelExit n cont is out ∧ c = ⟨s, f, out⟩ :=
  Proofs.Inversion.label_inv h rfl

/-- A handler steps inside (`ctxt-handler`) or by an exit rule (including catching). -/
theorem Step.handler_inv {n : Nat} {cs : List Catch} {is : List Admin}
    (h : Step P host ⟨s, f, [.handler n cs is]⟩ c) :
    (∃ s' f' is', Step P host ⟨s, f, is⟩ ⟨s', f', is'⟩ ∧ c = ⟨s', f', [.handler n cs is']⟩) ∨
      ∃ out, HandlerExit s f n cs is out ∧ c = ⟨s, f, out⟩ :=
  Proofs.Inversion.handler_inv h rfl

/-- A frame steps inside, in its own frame (`ctxt-frame`), or by an exit rule (values,
`return`, trap, exception, tail call). Neither alternative depends on the outer frame `f`. -/
theorem Step.frame_inv {n : Nat} {fi : Frame} {is : List Admin}
    (h : Step P host ⟨s, f, [.frame n fi is]⟩ c) :
    (∃ s' fi' is', Step P host ⟨s, fi, is⟩ ⟨s', fi', is'⟩ ∧ c = ⟨s', f, [.frame n fi' is']⟩) ∨
      ∃ out, FrameExit s fi n is out ∧ c = ⟨s, f, out⟩ :=
  Proofs.Inversion.frame_inv h rfl

/-- `LABEL_n{cont} (br 0)` only branches: `n = 0` and the continuation runs. -/
theorem Step.label_br_zero_inv {n : Nat} {cont : List Instr} {l : LabelIdx} (hl : l.toNat = 0)
    (h : Step P host ⟨s, f, [.label n cont [.plain (.br l)]]⟩ c) :
    n = 0 ∧ c = ⟨s, f, expression cont⟩ :=
  Proofs.Inversion.label_br_zero_inv h hl rfl

/-! ## `loop (br 0)` -/

theorem Step.loopBr0_inv {bt : BlockType} (h : Step P host (loopBr0 s f bt) c) :
    c = labelBr0 s f bt :=
  Proofs.Inversion.loopBr0_inv h

theorem Step.labelBr0_inv {bt : BlockType} (h : Step P host (labelBr0 s f bt) c) :
    c = loopBr0 s f bt :=
  Proofs.Inversion.labelBr0_inv h

theorem Step.loopBr0_step {bt : BlockType} {t₂ : List CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) :
    Step P host (loopBr0 s f bt) (labelBr0 s f bt) :=
  Proofs.Inversion.loopBr0_step hbt

theorem Step.labelBr0_step {bt : BlockType} : Step P host (labelBr0 s f bt) (loopBr0 s f bt) :=
  Proofs.Inversion.labelBr0_step

/-- Every configuration reachable from `loop bt (br 0)` is one of its two. -/
theorem loopBr0_reach {bt : BlockType} (h : Steps P host (loopBr0 s f bt) c) :
    c = loopBr0 s f bt ∨ c = labelBr0 s f bt :=
  Proofs.Inversion.loopBr0_reach h

theorem loopBr0_diverges {bt : BlockType} {t₂ : List CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) : Diverges P host (loopBr0 s f bt) :=
  Proofs.Inversion.loopBr0_diverges hbt

/-- `loop bt (br 0)` never reaches a result (values, trap or exception). -/
theorem loopBr0_not_terminal {bt : BlockType} (h : Steps P host (loopBr0 s f bt) c) :
    ¬ c.Terminal :=
  Proofs.Inversion.loopBr0_not_terminal h

end Silmaril.Wasm.Execution.Core
