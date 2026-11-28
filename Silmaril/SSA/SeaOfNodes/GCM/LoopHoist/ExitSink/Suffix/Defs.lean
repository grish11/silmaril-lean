module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Defs

/-! # Discover and sink a checked suffix into the existing loop exit -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Frame Terminator)
open Silmaril.MLIR.Pure (Operands i1)
open Silmaril.MLIR.SCF (For)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra Γ root moved args : List Width} {saved carried result w : Width}

/-- Reindex a variable through the removed suffix's result types. -/
def weakenFront : (moved : List Width) → Rename root (moved ++ root)
  | [], _, ref => ref
  | _ :: rest, _, ref => .there (weakenFront rest ref)

/-- Locate a guard or feedback read in the retained scope. -/
def unweakenFront? : (moved : List Width) → (ref : Var (moved ++ root) w) →
    Option { old : Var root w // weakenFront moved old = ref }
  | [], ref => some ⟨ref, rfl⟩
  | _ :: _, .here => none
  | _ :: rest, .there ref => do
    let old ← unweakenFront? rest ref
    pure ⟨old.1, congrArg Var.there old.2⟩

def unweakenPacket? (moved : List Width) : {args : List Width} →
    (reads : Operands (moved ++ root) args) →
    Option { packet : Operands root args // For.renameOperands (weakenFront moved) packet = reads }
  | _, .nil => some ⟨.nil, rfl⟩
  | _, .cons head tail => do
    let ref ← unweakenFront? moved head
    let rest ← unweakenPacket? moved tail
    pure ⟨.cons ref.1 rest.1, by
      change Operands.cons (weakenFront moved ref.1) (For.renameOperands (weakenFront moved) rest.1) = _
      rw [ref.2, rest.2]⟩

/-- Preserve exact references when the exit also receives ambient inputs. -/
def weakenEnd {Input : List Width} : {Γ : List Width} → Rename Γ (Γ ++ Input)
  | _, _, .here => .here
  | _, _, .there rest => .there (weakenEnd rest)

def scopeRefs : (Γ : List Width) → Operands Γ Γ
  | [] => .nil
  | _ :: rest => .cons .here (For.renameOperands Var.there (scopeRefs rest))

/-- A checked suffix has any sequence of typed pure lets, then a guard
and feedback packet entirely in the retained scope. The false-edge result
is produced by the suffix. -/
inductive Body (root : List Width) : (moved : List Width) →
      Block TargetOp (Label saved carried result extra) (moved ++ root) [result] → Type where
  | finish {moved : List Width} (guard : Var root i1) (feedback : Operands root (SavedBank saved carried extra))
      (value : Var (moved ++ root) result) (inside : value.index < moved.length) :
      Body root moved (.terminator (.condBr (weakenFront moved guard)
        ⟨.header, For.renameOperands (weakenFront moved) feedback⟩ ⟨.exit, .cons value .nil⟩))
  | bind {moved args : List Width} {w : Width} (op : TargetOp args w) (operands : Operands (moved ++ root) args)
      {rest : Block TargetOp (Label saved carried result extra) ((w :: moved) ++ root) [result]}
      (tail : Body root (w :: moved) rest) : Body root moved (.letOp op operands rest)

def Body.finish? (moved : List Width) :
    (term : Terminator (Label saved carried result extra) [result] (moved ++ root)) →
    Option (Body root moved (.terminator term))
  | .condBr guard ⟨.header, feedback⟩ ⟨.exit, .cons value .nil⟩ => do
    if inside : value.index < moved.length then
      let test ← unweakenFront? moved guard
      let packet ← unweakenPacket? moved feedback
      pure (by rw [← test.2, ← packet.2]; exact .finish test.1 packet.1 value inside)
    else none
  | _ => none

def Body.check? : (moved : List Width) →
    (code : Block TargetOp (Label saved carried result extra) (moved ++ root) [result]) →
    Option (Body root moved code)
  | moved, .letOp (w := width) op operands rest =>
    (check? (width :: moved) rest).map (.bind op operands)
  | moved, .terminator term => finish? moved term
termination_by _ code => (shape.ofBlock code).bindings
decreasing_by simp [shape.ofBlock]

def Body.transfers {moved : List Width}
    {original : Block TargetOp (Label saved carried result extra) (moved ++ root) [result]}
    (body : Body root moved original) : Var root i1 × Operands root (SavedBank saved carried extra) :=
  match body with
  | .finish guard feedback .. => (guard, feedback)
  | .bind _ _ tail => tail.transfers

def Body.exitCode {moved : List Width}
    {original : Block TargetOp (Label saved carried result extra) (moved ++ root) [result]}
    (body : Body root moved original) (Input : List Width) :
    Block TargetOp (ExitLabel (SavedBank saved carried extra) root) ((moved ++ root) ++ Input) [result] :=
  match body with
  | .finish _ _ value _ => .terminator (.ret (.cons (weakenEnd value) .nil))
  | .bind op operands tail => .letOp op (For.renameOperands weakenEnd operands) (tail.exitCode Input)

def Body.value {moved : List Width}
    {original : Block TargetOp (Label saved carried result extra) (moved ++ root) [result]}
    (body : Body root moved original) (env : Env (moved ++ root)) : BitVec result.val :=
  match body with
  | .finish _ _ read _ => env.get read
  | .bind op reads tail => tail.value (.cons (evalOp op (reads.eval env)) env)

inductive Header : Nat → {Γ : List Width} →
      Block TargetOp (Label saved carried result extra) Γ [result] → Type where
  | split {Γ : List Width} {tail : Block TargetOp (Label saved carried result extra) Γ [result]}
      (body : Body Γ [] tail) : Header 0 tail
  | keep {cut : Nat} {Γ args : List Width} {w : Width} (op : TargetOp args w) (operands : Operands Γ args)
      {rest : Block TargetOp (Label saved carried result extra) (w :: Γ) [result]}
      (tail : Header cut rest) : Header (cut + 1) (.letOp op operands rest)

def Header.check? : (cut : Nat) → {Γ : List Width} →
    (original : Block TargetOp (Label saved carried result extra) Γ [result]) → Option (Header cut original)
  | 0, _, original => (Body.check? [] original).map .split
  | cut + 1, _, .letOp op operands rest => (check? cut rest).map (.keep op operands)
  | _ + 1, _, .terminator _ => none

def Header.packetTypes {cut : Nat} {Γ : List Width}
    {original : Block TargetOp (Label saved carried result extra) Γ [result]} (header : Header cut original) : List Width :=
  match header with
  | .split (Γ := root) _ => root
  | .keep _ _ tail => tail.packetTypes

def Header.code {cut : Nat} {Γ : List Width}
    {original : Block TargetOp (Label saved carried result extra) Γ [result]} (header : Header cut original) :
    Block TargetOp (ExitLabel (SavedBank saved carried extra) header.packetTypes) Γ [result] :=
  match header with
  | .split (Γ := root) body => .terminator (.condBr body.transfers.1
      ⟨.header, body.transfers.2⟩ ⟨.exit, scopeRefs root⟩)
  | .keep op operands tail => .letOp op operands tail.code

def Header.exitCode {cut : Nat} {Γ : List Width}
    {original : Block TargetOp (Label saved carried result extra) Γ [result]} (header : Header cut original) (Input : List Width) :
    Block TargetOp (ExitLabel (SavedBank saved carried extra) header.packetTypes)
      (header.packetTypes ++ Input) [result] :=
  match header with
  | .split body => body.exitCode Input
  | .keep _ _ tail => tail.exitCode Input

def Header.value {cut : Nat} {Γ : List Width}
    {original : Block TargetOp (Label saved carried result extra) Γ [result]} (header : Header cut original) (packet : Env header.packetTypes) : BitVec result.val :=
  match header with
  | .split body => body.value packet
  | .keep _ _ tail => tail.value packet

/-- Interpret the moved suffix only on the old exit transfer. -/
def restorePacketWith (compute : Env root → BitVec result.val) :
    Frame (ExitLabel (SavedBank saved carried extra) root) → Frame (Label saved carried result extra)
  | ⟨.header, packet⟩ => ⟨.header, packet⟩
  | ⟨.exit, packet⟩ => ⟨.exit, .cons (compute packet) .nil⟩

def Header.restorePacket {cut : Nat} {original : Block TargetOp (Label saved carried result extra) Γ [result]}
    (header : Header cut original) :
    Frame (ExitLabel (SavedBank saved carried extra) header.packetTypes) →
      Frame (Label saved carried result extra) :=
  restorePacketWith header.value

structure Emission (source : Source Input saved carried result extra) (cut : Nat) where
  entry : Entry source.entry
  header : Header cut (source.block .header)
  returns : source.block .exit = .terminator (.ret (.cons .here .nil))

variable {source : Source Input saved carried result extra} {cut : Nat}

def Emission.cfg (emission : Emission source cut) :
    TargetCfg Input saved carried result extra emission.header.packetTypes where
  entry := emission.entry.code _
  block
    | .header => emission.header.code
    | .exit => emission.header.exitCode Input

abbrev Emission.restorePacket (emission : Emission source cut) := emission.header.restorePacket

structure Site (Labels : List Width → Type) where
  point : Point Labels
  operands : List (Point Labels)
  uses : List (Use Labels)

/-- At cut k, the first k de Bruijn references are local definitions,
in reverse order. All older reads are already available at block entry. -/
def operandSites {Labels : List Width → Type} (block : BlockId Labels) (cut : Nat) :
    {Γ args : List Width} → Operands Γ args → List (Point Labels)
  | _, _, .nil => []
  | _, _, .cons ref rest => ⟨block, cut - ref.index⟩ :: operandSites block cut rest

/-- Collect actual operand sites and ordinary or edge-occurrence uses of
each emitted definition. The exit uses the same site collector as a CFG cut. -/
def sites {Labels : List Width → Type} {Result : List Width} (block : BlockId Labels) :
    (cut : Nat) → {Γ : List Width} → Block TargetOp Labels Γ Result → List (Site Labels)
  | _, _, .terminator _ => []
  | cut, _, .letOp _ reads tail =>
    ⟨⟨block, cut⟩, operandSites block cut reads, useSitesAt block 0 (cut + 1) tail⟩ ::
      sites block (cut + 1) tail

def checkExit (emission : Emission source cut) : Bool :=
  let _ := targetDecEq (saved := saved) (carried := carried) (extra := extra)
    (args := emission.header.packetTypes)
  (sites exitId 0 (emission.cfg.block .exit)).all fun site =>
    Dominance.Placement.checkCut emission.cfg targets site.operands site.uses site.point

def admitAt? (source : Source Input saved carried result extra) (cut : Nat) : Option (Emission source cut) := do
  let entry ← Entry.check? source.entry
  let header ← Header.check? cut (source.block .header)
  match returns : source.block .exit with
  | .terminator (.ret (.cons .here .nil)) => some ⟨entry, header, returns⟩
  | _ => none

/-- Check a nominated split on the current header. -/
def sinkAt? (source : Source Input saved carried result extra) (cut : Nat) : Option (Emission source cut) :=
  (admitAt? source cut).filter checkExit

def cuts (source : Source Input saved carried result extra) : List Nat :=
  List.range (shape source (some ⟨_, .header⟩)).bindings

/-- Visit the actual header cuts in increasing order to find the longest
admitted nonempty suffix. Recheck all sites on each actual emitted exit. -/
def discover? (source : Source Input saved carried result extra) : Option ((cut : Nat) × Emission source cut) :=
  (cuts source).findSome? fun cut => (sinkAt? source cut).map (⟨cut, ·⟩)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix
