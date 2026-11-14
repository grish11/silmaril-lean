module

public import Silmaril.Wasm.Cfg.BlockTree.Defs
public import Silmaril.Wasm.Validation.Check.Validate

@[expose] public section

/-!
# Typed basic blocks: the interface of each block of a function body

A block's **interface** is relative to a static context (`Validation.Context`). The context
holds the fixed module environment, the function's local *types* and their initialisation state,
the label stack of the enclosing structured instructions, and the return type. Local *values*
are not here: they belong to the activation frame of a run, apart from the module store. The
operand stack is explicit: the block's instructions take the stack `inStk` (padded with `pad`
copies of `⊥` after an unconditional branch) to `outStk`, initialising the locals `inits`.

`bodyIfaces C body` computes these interfaces for every block. It runs the validator's
instruction checker (`checkSeq`, which `checkModule?` uses) on each block's instructions,
threading the context and the stack through the body: label pushes come from the block types,
and local initialisation from the checker. The checker only records interfaces it can justify:
`bodyIfaces_typed` (in `Thms`) proves each recorded interface is an `Instrs_ok` derivation.
That is a typing fact about the block's instructions under its context. It is not yet a
statement about runs.
-/

namespace Silmaril.Wasm.Cfg

open Silmaril.Wasm.Validation

/-- The interface of one block: its identity, its static context, its instructions (the
segment, terminator included), and the stack and local-initialisation effect of those
instructions. -/
structure BlockIface where
  id : BlockId
  ctx : Context
  instrs : List Instr
  pad : Nat
  inStk : List CValType
  inits : List Nat
  outStk : List CValType

/-- **The typing claim of an interface**: `Instrs_ok` of its instructions under its context. -/
def BlockIface.Typed (x : BlockIface) : Prop :=
  InstrsOk x.ctx x.instrs ⟨List.replicate x.pad .botv ++ x.inStk, x.inits, x.outStk⟩

/-- Check one block's instructions from stack `s` (polymorphic after an unconditional branch). -/
def ifaceOf? (id : BlockId) (C : Context) (s : List CValType) (poly : Bool) (is : List Instr) :
    Option BlockIface :=
  if resOk tyOkC C.toTypeCtx s then
    match checkSeq atomC tyOkC C s poly none is with
    | some (out, xs, k) => some ⟨id, C, is, k, s, xs, out⟩
    | none => none
  else none

/-- Terminators after which the stack is polymorphic. -/
def uncond : Instr → Bool
  | .br _ | .brTable .. | .return_ | .returnCall _ | .returnCallRef _ | .returnCallIndirect ..
  | .unreachable | .throw _ | .throwRef => true
  | _ => false

mutual
/-- The interfaces of a sequence at `path`, from block `k`, under context `C` and stack `s`,
with the simple instructions `acc` (reversed) of the current block. -/
def typeWalk (path : List SeqStep) (k : Nat) (C : Context) (s : List CValType) (poly : Bool)
    (acc : List Instr) : List Instr → List BlockIface
  | [] => if acc.isEmpty then [] else (ifaceOf? ⟨path, k⟩ C s poly acc.reverse).toList
  | i :: is =>
    if isTerminator i then
      (ifaceOf? ⟨path, k⟩ C s poly (acc.reverse ++ [i])).toList ++
        ((match checkSeq atomC tyOkC C s poly none acc.reverse with
          | some (_, xs, _) => typeNested path k (C.initLocals xs) i
          | none => []) ++
        (match checkSeq atomC tyOkC C s poly none (acc.reverse ++ [i]) with
          | some (out, xs, _) =>
            typeWalk path (k + 1) (C.initLocals xs) (if uncond i then [] else out) (uncond i) [] is
          | none => []))
    else typeWalk path k C s poly (i :: acc) is
/-- The interfaces of the sequences terminator `i` of block `k` opens, under context `C`. -/
def typeNested (path : List SeqStep) (k : Nat) (C : Context) : Instr → List BlockIface
  | .block bt b | .tryTable bt _ b =>
    match CheckInstrs.blockType? tyOkC C bt with
    | some (t₁, t₂) => typeWalk (path ++ [(k, 0)]) 0 (C.withLabel t₂) t₁ false [] b
    | none => []
  | .loop bt b =>
    match CheckInstrs.blockType? tyOkC C bt with
    | some (t₁, _) => typeWalk (path ++ [(k, 0)]) 0 (C.withLabel t₁) t₁ false [] b
    | none => []
  | .if_ bt t e =>
    match CheckInstrs.blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      typeWalk (path ++ [(k, 0)]) 0 (C.withLabel t₂) t₁ false [] t ++
        typeWalk (path ++ [(k, 1)]) 0 (C.withLabel t₂) t₁ false [] e
    | none => []
  | _ => []
end

/-- **The block interfaces of a body** under the function's context `C` (`Context.funcBody`). -/
def bodyIfaces (C : Context) (body : Expr) : List BlockIface := typeWalk [] 0 C [] false [] body

end Silmaril.Wasm.Cfg
