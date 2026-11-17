module

public import Silmaril.Wasm.Cfg.MachineL.Defs
public import Silmaril.Wasm.Interp.Defs
public import Silmaril.Wasm.Abstract.CallX.Defs
public import Silmaril.Wasm.Abstract.CallXE.Defs
public import Silmaril.Wasm.Abstract.CallXP.Defs
public import Silmaril.Wasm.Cfg.Bridge.Defs

@[expose] public section

/-!
# Projecting the logged machine to `MStepC`: definitions

`PopFit f k ls stk`: leaving `k` sequences from the label frames `ls` with the stack `stk` (bottom
first), each left frame's block type has arities (`Binaryen.arity`), and the stack at each level
has at most that frame's result arity. On such stacks the logged machine's native frame popping
(`popN`, which keeps the top `nr` values) is `MStepC`'s Core popping (`popL`, which keeps the
whole stack). Typed code leaves an arm normally with exactly its result arity.

**The checker invariant** (`CInv`), toward the stepwise projection: at a block state, the rest of
its sequence passes the arity check `chkE ext` (for exceptions, `ehExt tags`) at the stack's height,
under the label arities the frames record (`labs`: innermost first, then the function label).
Each frame (`ChkF`) records:
* its structured instruction, and the block type's arities (`blockArity`);
* its label arity (parameters for a `loop`, results otherwise);
* that the current sequence ends at the frame's result arity (`endsAt`);
* the check of its arm from its parameters;
* the check of the parent's rest after it, at the height its outer values and results make.

The function's level ends at its result arity. `NoTry body`: no segment ends in a `try_table`. This
is the fragment without handlers; catching belongs to the exception bridge.

**Straight-line code** (`Flat`): no terminator, and no indirect or reference call. Segment bodies
have no terminators; under `DirectCalls body` they are `Flat`.

**Pending tail calls on straight-line code** (`ResOutP`): how a native body result with pending
tail calls (`CallXP.POut`) and a region outcome end alike. A flow ends as `Bridge.FlowRel` says,
in the same store and frame. A pending tail call `tail a args n` is the region's pending tail
call of `a` over `W`, not answered: in the same store and frame, `args` are the top values of
`W` (bottom first), as many as the callee's parameters, and `n` is the callee's result count.

Theorems in `Silmaril.Wasm.Cfg.MachineLProj.Thms`.
-/

namespace Silmaril.Wasm.Cfg.MachineL

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Binaryen Silmaril.Wasm.Interp

variable {H : Type}

/-- **The stack fits each level left**: leaving `k` sequences, each left frame's block type has
arities, and the stack at that level has at most its result arity. -/
def PopFit (f : Frame) : Nat → List LFrame → List Val → Prop
  | 0, _, _ => True
  | _ + 1, [], _ => False
  | k + 1, L :: ls, stk => ∃ np nr, Binaryen.arity f L.bt = some (np, nr) ∧ stk.length ≤ nr ∧
      PopFit f k ls (L.outer ++ stk)

/-- The label arities in scope: the frames' recorded arities, innermost first, then the function
label (the function's result arity). -/
def labs (ret : Nat) (ls : List LFrame) : List Nat := ls.map LFrame.arity ++ [ret]

section
variable (ext : ExtArity H) (F : List (FuncInst H)) (mi : ModuleInst) (nl ret : Nat) (body : Expr)

/-- **Checked frames** at reversed path `rp`, the current sequence ending at `out`. -/
def ChkF : List SeqStep → List LFrame → Option Nat → Prop
  | [], [], out => endsAt (some out) ret = true
  | (m, a) :: rp, L :: ls, out => ∃ (pc : List Instr) (sg : Segment) (t : Instr) (c : List Instr)
      (np nr : Nat), seqAt body rp.reverse = some pc ∧ (segment pc)[m]? = some sg ∧
      sg.term = some t ∧ armOf t a = some c ∧ StructKind t L.bt L.loop L.tryT L.catches ∧
      blockArity mi L.bt = some (np, nr) ∧ L.arity = (if L.loop then np else nr) ∧
      endsAt (some out) nr = true ∧
      (∃ oa, chkE ext F mi nl ret (labs ret (L :: ls)) (some np) (liftInstrs c) = some oa ∧
        endsAt (some oa) nr = true) ∧
      ∃ out', chkE ext F mi nl ret (labs ret ls) (some (L.outer.length + nr))
        (liftInstrs (restAt pc (m + 1))) = some out' ∧ ChkF rp ls out'
  | _, _, _ => False

/-- **The checker invariant of a block state**: the rest of its sequence passes the check at the
stack's height, under checked frames. Other states: no condition. -/
def CInv (st : MState H) : Prop :=
  match st.node with
  | .block b => st.frame.module = mi ∧ ∃ (c : List Instr) (out : Option Nat),
      seqAt body b.seq = some c ∧
      chkE ext F mi nl ret (labs ret st.lbls) (some st.stk.length) (liftInstrs (restAt c b.idx)) =
        some out ∧ ChkF ext F mi nl ret body b.seq.reverse st.lbls out
  | _ => True

end

/-- **No `try_table`**: no segment of the body ends in a `try_table` (the fragment without
handlers; catching is the exception bridge's). -/
def NoTry (body : Expr) : Prop :=
  ∀ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (bt : BlockType)
    (cs : List Catch) (b : List Instr), seqAt body p = some c → (segment c)[i]? = some sg →
    sg.term ≠ some (.tryTable bt cs b)

/-- Straight-line code: no terminator (so no structured instruction and no exception form), and
no indirect or reference call. -/
def Flat (is : List Instr) : Prop :=
  ∀ i ∈ is, isTerminator i = false ∧ Abstract.CallX.isXCall i = false

/-- **Direct calls only**: no segment body makes an indirect or reference call (`call_indirect`,
`call_ref`). On such bodies the logged and the legacy native semantics agree on straight-line code
(`CallXP.evalOXP_iff_evalOXE`); the general case belongs to the pending-call bridge. -/
def DirectCalls (body : Expr) : Prop :=
  ∀ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment), seqAt body p = some c →
    (segment c)[i]? = some sg → ∀ x ∈ sg.body, Abstract.CallX.isXCall x = false

/-- **Plain terminators**: no segment ends in an exception form (`throw`, `throw_ref`) or an
extended call form (`call_indirect`, `call_ref`, the tail calls). With `NoTry`, the remaining
terminators are the structured ones, the branches, `return` and `unreachable`. -/
def PlainTerms (body : Expr) : Prop :=
  ∀ (p : List SeqStep) (c : List Instr) (i : Nat) (sg : Segment) (t : Instr),
    seqAt body p = some c → (segment c)[i]? = some sg → sg.term = some t →
      Abstract.CallXE.ehInstr t = false ∧ Abstract.CallX.isXCall t = false

/-- **The stepwise projection relation** between a logged machine state and an `MStepC` state:
equal, or both `exit` with no frames, the same store and frame, and the `MStepC` stack the
logged one under further values (`MStepC` keeps the outer values of the frames a `return` or a
branch to the function label leaves, `brVals`; `MStepL` keeps the branch-site stack only). -/
def ProjRel (stL stC : MState H) : Prop :=
  stC = stL ∨ (stL.node = .exit ∧ stC.node = .exit ∧ stL.lbls = [] ∧ stC.lbls = [] ∧
    stC.store = stL.store ∧ stC.frame = stL.frame ∧ ∃ junk, stC.stk = junk ++ stL.stk)

/-- **A native body result with pending tail calls and a region outcome that end alike.**
* A flow `fl`: the same store and frame, and `Bridge.FlowRel fl o` (so `o` is not a pending
  tail call; a native trap may be a region pending tail call of null).
* A pending tail call of `a` on `args` with result count `n`: the region ends in a pending tail
  call `.tail W a c` of the same callee, `c` a `return_call_ref` form, in the same store and
  frame; the callee `fi` at `a` in that store has parameters `ps` and results `rs`, `W` is
  `W₀ ++ args` with `args.length = ps.length` (the top `ps.length` values of `W`, bottom first),
  and `n = rs.length`. -/
def ResOutP (s' : Store H) (f' : Frame) (o : Region.Out) :
    Store H × Frame × Abstract.CallXP.POut → Prop
  | (s₂, f₂, .flow fl) => s₂ = s' ∧ f₂ = f' ∧ Bridge.FlowRel fl o
  | (s₂, f₂, .tail a args n) => ∃ (W : List Val) (c : Admin), o = .tail W a c ∧
      c.IsReturnCallRef ∧ s₂ = s' ∧ f₂ = f' ∧
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType) (W₀ : List Val),
        s'.funcs[a]? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        W = W₀ ++ args ∧ args.length = ps.length ∧ n = rs.length

end Silmaril.Wasm.Cfg.MachineL
