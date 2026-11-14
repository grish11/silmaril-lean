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
threading the checker's state (`CkSt`: context, stack, polymorphic) through the body, one
`checkSeq` step at a time (`ckStep`): label pushes come from the block types, local
initialisation from the checker. The checker only records interfaces it can justify:
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

/-- The validator's checker state between two instructions: the context (with the locals
initialised so far), the operand stack, and whether the stack is polymorphic (after an
unconditional branch). -/
structure CkSt where
  C : Context
  s : List CValType
  poly : Bool

/-- One step of the validator's sequence checker `checkSeq` (with no goal stack). -/
def ckStep (st : CkSt) (i : Instr) : Option CkSt :=
  match checkInstr atomC tyOkC st.C (padStack (padFor st.C st.poly i) st.s) i with
  | some (.normal n xs out) =>
    if localsOk st.C xs && resOk tyOkC st.C.toTypeCtx out then
      some ⟨st.C.initLocals xs, st.s.take (st.s.length - n) ++ out, st.poly⟩
    else none
  | some (.poly _) => some ⟨st.C, [], true⟩
  | none => none

/-- The checker run over a sequence. -/
def ckRun (st : CkSt) (l : List Instr) : Option CkSt := l.foldlM ckStep st

/-- Check one block's instructions from the checker state `st`. -/
def ifaceOf? (id : BlockId) (st : CkSt) (is : List Instr) : Option BlockIface :=
  if resOk tyOkC st.C.toTypeCtx st.s then
    match checkSeq atomC tyOkC st.C st.s st.poly none is with
    | some (out, xs, k) => some ⟨id, st.C, is, k, st.s, xs, out⟩
    | none => none
  else none

mutual
/-- The interfaces of a sequence at `path`, from block `k`, from the checker state `st` at the
start of the current block, whose simple instructions so far are `acc` (reversed). -/
def typeWalk (path : List SeqStep) (k : Nat) (st : CkSt) (acc : List Instr) :
    List Instr → List BlockIface
  | [] => if acc.isEmpty then [] else (ifaceOf? ⟨path, k⟩ st acc.reverse).toList
  | i :: is =>
    if isTerminator i then
      (ifaceOf? ⟨path, k⟩ st (acc.reverse ++ [i])).toList ++
        ((match ckRun st acc.reverse with
          | some st' => typeNested path k st'.C i
          | none => []) ++
        (match ckRun st (acc.reverse ++ [i]) with
          | some st' => typeWalk path (k + 1) st' [] is
          | none => []))
    else typeWalk path k st (i :: acc) is
/-- The interfaces of the sequences terminator `i` of block `k` opens, under context `C` (the
context at the terminator). -/
def typeNested (path : List SeqStep) (k : Nat) (C : Context) : Instr → List BlockIface
  | .block bt b | .tryTable bt _ b =>
    match CheckInstrs.blockType? tyOkC C bt with
    | some (t₁, t₂) => typeWalk (path ++ [(k, 0)]) 0 ⟨C.withLabel t₂, t₁, false⟩ [] b
    | none => []
  | .loop bt b =>
    match CheckInstrs.blockType? tyOkC C bt with
    | some (t₁, _) => typeWalk (path ++ [(k, 0)]) 0 ⟨C.withLabel t₁, t₁, false⟩ [] b
    | none => []
  | .if_ bt t e =>
    match CheckInstrs.blockType? tyOkC C bt with
    | some (t₁, t₂) =>
      typeWalk (path ++ [(k, 0)]) 0 ⟨C.withLabel t₂, t₁, false⟩ [] t ++
        typeWalk (path ++ [(k, 1)]) 0 ⟨C.withLabel t₂, t₁, false⟩ [] e
    | none => []
  | _ => []
end

/-- **The block interfaces of a body** under the function's context `C` (`Context.funcBody`). -/
def bodyIfaces (C : Context) (body : Expr) : List BlockIface := typeWalk [] 0 ⟨C, [], false⟩ [] body

end Silmaril.Wasm.Cfg
