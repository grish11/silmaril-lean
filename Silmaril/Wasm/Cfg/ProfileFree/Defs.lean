module

public import Silmaril.Wasm.Cfg.DanglingTyped.Defs

@[expose] public section

/-!
# Profile-free Core code: definitions

A Core step reads the numeric profile `Numerics.Profile` (`nd`, `relaxed`, `nan`, `grow`) only in
the premises of the floating-point unary and binary operations, the conversions, the vector
operations, and `memory.grow`/`table.grow`. Code without these instructions takes the same steps
at every profile.

* `PSens i`: the flat instructions whose Core rules read the profile: `fN.unop`, `fN.binop`,
  every conversion, every vector operation except `v128.const`, `memory.grow` and `table.grow`;
* `IFree i`: no profile-sensitive instruction, also in nested bodies (structured instructions
  `DanglingTyped.Structured` recurse);
* `AFree a`: the same on administrative code (labels: continuation and body; handlers and
  frames: body);
* `FuncsFree F`: every Wasm function of `F` has a profile-free body (host functions run no
  code);
* **`ConfigFree c`**: profile-free code in a store with profile-free functions;
* `HostFree host`: every host answer keeps the functions profile-free (store-preserving hosts
  do).

The checker's instruction profile (`Interp.CheckComplete.StoreSupported`, `XProfile.xInstr`) has
no profile-sensitive instruction. Unlike `DanglingTyped.ISupp`, `IFree` allows type tests and
aggregates: it constrains only what the profile can change.

Theorems in `Silmaril.Wasm.Cfg.ProfileFree.Thms`.
-/

namespace Silmaril.Wasm.Cfg.ProfileFree

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Cfg.DanglingTyped

variable {H : Type}

/-- **Flat instructions whose Core rules read the numeric profile.** -/
def PSens : Instr → Prop
  | .floatUnOp .. | .floatBinOp .. | .convert _ | .memoryGrow _ | .tableGrow _ => True
  | .vecUnOp _ | .vecBinOp _ | .vecTernOp _ | .vecTestOp _ | .vecIntUnOp .. | .vecFloatUnOp ..
  | .vecIntBinOp .. | .vecFloatBinOp .. | .vecIntTernOp .. | .vecFloatTernOp .. | .vecAllTrue _
  | .vecIntRelOp .. | .vecFloatRelOp .. | .vecShiftOp .. | .vecBitmask _ | .vecSwizzle _
  | .vecShuffle _ | .vecExtUnOp .. | .vecExtBinOp .. | .vecExtTernOp .. | .vecNarrow ..
  | .vecConvert .. | .vecSplat _ | .vecExtractLane .. | .vecReplaceLane .. => True
  | _ => False

/-- **A profile-free instruction**: no profile-sensitive instruction, also in nested bodies. -/
inductive IFree : Instr → Prop where
  | block (bt : BlockType) {body : List Instr} (h : ∀ i ∈ body, IFree i) : IFree (.block bt body)
  | loop (bt : BlockType) {body : List Instr} (h : ∀ i ∈ body, IFree i) : IFree (.loop bt body)
  | if_ (bt : BlockType) {b₁ b₂ : List Instr} (h₁ : ∀ i ∈ b₁, IFree i) (h₂ : ∀ i ∈ b₂, IFree i) :
      IFree (.if_ bt b₁ b₂)
  | tryTable (bt : BlockType) (cs : List Catch) {body : List Instr} (h : ∀ i ∈ body, IFree i) :
      IFree (.tryTable bt cs body)
  | atom {i : Instr} (hs : ¬ Structured i) (hn : ¬ PSens i) : IFree i

/-- **Profile-free administrative code.** -/
inductive AFree : Admin → Prop where
  | plain {i : Instr} (h : IFree i) : AFree (.plain i)
  | ref (r : Ref) : AFree (.ref r)
  | callRefType (d : DefType) : AFree (.callRefType d)
  | returnCallRefType (d : DefType) : AFree (.returnCallRefType d)
  | label (n : Nat) {cont : List Instr} {body : List Admin} (hc : ∀ i ∈ cont, IFree i)
      (hb : ∀ a ∈ body, AFree a) : AFree (.label n cont body)
  | handler (n : Nat) (cs : List Catch) {body : List Admin} (hb : ∀ a ∈ body, AFree a) :
      AFree (.handler n cs body)
  | frame (n : Nat) (fr : Frame) {body : List Admin} (hb : ∀ a ∈ body, AFree a) :
      AFree (.frame n fr body)
  | trap : AFree .trap

/-- **Profile-free functions**: every Wasm function has a profile-free body. -/
def FuncsFree (F : List (FuncInst H)) : Prop :=
  ∀ fi ∈ F, ∀ code, fi.code = .wasm code → ∀ i ∈ code.body, IFree i

/-- **A profile-free configuration**: profile-free code, profile-free functions. -/
def ConfigFree (c : Config H) : Prop := (∀ a ∈ c.code, AFree a) ∧ FuncsFree c.store.funcs

/-- **A host keeping functions profile-free.** -/
def HostFree (host : HostSemantics H) : Prop :=
  ∀ (hh : H) (s : Store H) (us : List Val) (s' : Store H) (r : Result),
    host hh s us (.returned s' r) → FuncsFree s.funcs → FuncsFree s'.funcs

end Silmaril.Wasm.Cfg.ProfileFree
