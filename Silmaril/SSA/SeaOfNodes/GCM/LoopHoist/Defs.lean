module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Defs

/-! # Hoist an invariant binding of the existing pure typed loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.SCF (For)
open Loop.MLIR.CF (Program TargetOp evalOp lower)

abbrev SourceLabel := Loop.MLIR.CF.Label

/-- The header receives the saved values before the original latch word. -/
inductive Label (saved carried result : Width) (extra : List Width := []) : List Width → Type where
  | header : Label saved carried result extra ((extra ++ [saved]) ++ [carried])
  | exit : Label saved carried result extra [result]

abbrev Output (Input : List Width) (carried result : Width) :=
  (saved : Width) × Cfg TargetOp (Label saved carried result) Input [result]

variable {Input Γ Δ args : List Width} {saved carried result w : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

def headerId : BlockId (SourceLabel carried result) := some ⟨_, .header⟩

def blocks : List (Target (SourceLabel carried result)) := [⟨_, .header⟩, ⟨_, .exit⟩]

/-- At header entry, index zero is the latch. Larger indices are immutable
function inputs, already available at preheader cut zero. -/
def operandSites : {args : List Width} → Operands (carried :: Input) args → List (Point (SourceLabel carried result))
  | _, .nil => []
  | _, .cons ref tail =>
    ⟨if ref.index == 0 then headerId else none, 0⟩ :: operandSites tail

/-- Translate a header operand list to entry scope when it reads only captures. -/
def capture? : {args : List Width} → Operands (carried :: Input) args → Option (Operands Input args)
  | _, .nil => some .nil
  | _, .cons .here _ => none
  | _, .cons (.there ref) tail => (capture? tail).map (.cons ref)

def positions (index : Nat) : {args : List Width} → Operands Γ args → Nat → List Nat
  | _, .nil, _ => []
  | _, .cons ref rest, slot =>
    let later := positions index rest (slot + 1)
    if ref.index == index then slot :: later else later

def useSitesAt {Labels : List Width → Type} {Result : List Width}
    (block : BlockId Labels) (index cut : Nat) : {Γ : List Width} →
    Block TargetOp Labels Γ Result → List (Use Labels)
  | _, .letOp _ operands rest =>
    let later := useSitesAt block (index + 1) (cut + 1) rest
    if (positions index operands 0).isEmpty then later else .ordinary ⟨block, cut⟩ :: later
  | _, .terminator (.br edge) =>
    (positions index edge.args 0).map (.phi block .jump)
  | _, .terminator (.condBr test onTrue onFalse) =>
    let guard := if test.index == index then [.ordinary ⟨block, cut⟩] else []
    guard ++ (positions index onTrue.args 0).map (.phi block .onTrue) ++
      (positions index onFalse.args 0).map (.phi block .onFalse)
  | _, .terminator (.ret values) =>
    if (positions index values 0).isEmpty then [] else [.ordinary ⟨block, cut⟩]

def useSites (index cut : Nat) {Γ : List Width} :
    Block TargetOp (SourceLabel carried result) Γ [result] → List (Use (SourceLabel carried result)) :=
  useSitesAt headerId index cut

abbrev Rename (Γ Δ : List Width) := ∀ {w}, Var Γ w → Var Δ w

def under (rename : Rename Γ Δ) : Rename (w :: Γ) (w :: Δ)
  | _, .here => .here
  | _, .there ref => .there (rename ref)

def appendOperands (tail : Operands Γ args) :
    {front : List Width} → Operands Γ front → Operands Γ (front ++ args)
  | _, .nil => tail
  | _, .cons head rest => .cons head (appendOperands tail rest)

variable {extra : List Width}

def routeEdgeWith (rename : Rename Γ Δ) (kept : Operands Δ (extra ++ [saved])) :
    Edge (SourceLabel carried result) Γ → Edge (Label saved carried result extra) Δ
  | ⟨.header, args⟩ => ⟨.header, appendOperands (For.renameOperands rename args) kept⟩
  | ⟨.exit, args⟩ => ⟨.exit, For.renameOperands rename args⟩

def routeTermWith (rename : Rename Γ Δ) (kept : Operands Δ (extra ++ [saved])) :
    Terminator (SourceLabel carried result) [result] Γ →
      Terminator (Label saved carried result extra) [result] Δ
  | .br edge => .br (routeEdgeWith rename kept edge)
  | .condBr test onTrue onFalse =>
    .condBr (rename test) (routeEdgeWith rename kept onTrue) (routeEdgeWith rename kept onFalse)
  | .ret values => .ret (For.renameOperands rename values)

def routeCodeWith : {Γ Δ : List Width} → Rename Γ Δ → Operands Δ (extra ++ [saved]) →
    Block TargetOp (SourceLabel carried result) Γ [result] →
      Block TargetOp (Label saved carried result extra) Δ [result]
  | _, _, rename, kept, .terminator term => .terminator (routeTermWith rename kept term)
  | _, _, rename, kept, .letOp op operands rest =>
    .letOp op (For.renameOperands rename operands)
      (routeCodeWith (under rename) (For.renameOperands Var.there kept) rest)

def routeEdge (rename : Rename Γ Δ) (keep : Var Δ saved)
    (edge : Edge (SourceLabel carried result) Γ) : Edge (Label saved carried result) Δ :=
  routeEdgeWith rename (.cons keep .nil) edge

def routeTerm (rename : Rename Γ Δ) (keep : Var Δ saved)
    (term : Terminator (SourceLabel carried result) [result] Γ) :
    Terminator (Label saved carried result) [result] Δ :=
  routeTermWith rename (.cons keep .nil) term

def routeCode (rename : Rename Γ Δ) (keep : Var Δ saved)
    (code : Block TargetOp (SourceLabel carried result) Γ [result]) :
    Block TargetOp (Label saved carried result) Δ [result] :=
  routeCodeWith rename (.cons keep .nil) code

def emitHeader (entry : Block TargetOp (SourceLabel carried result) Input [result])
    (op : TargetOp args saved) (captured : Operands Input args)
    (header : Block TargetOp (Label saved carried result) (saved :: carried :: Input) [result]) :
    Cfg TargetOp (Label saved carried result) Input [result] where
  entry := .letOp op captured (routeCode Var.there .here entry)
  block
    | .header => header
    | .exit => .terminator (.ret (.cons .here .nil))

/-- The old first header binding becomes a parameter for the remainder. -/
def emit (entry : Block TargetOp (SourceLabel carried result) Input [result])
    (op : TargetOp args saved) (captured : Operands Input args)
    (rest : Block TargetOp (SourceLabel carried result) (saved :: carried :: Input) [result]) :
    Cfg TargetOp (Label saved carried result) Input [result] :=
  emitHeader entry op captured (routeCode (fun ref => ref) .here rest)

def carryFrameWith (values : Env (extra ++ [saved])) :
    Frame (SourceLabel carried result) → Frame (Label saved carried result extra)
  | ⟨.header, args⟩ => ⟨.header, values.append args⟩
  | ⟨.exit, args⟩ => ⟨.exit, args⟩

def carryFrame (value : BitVec saved.val) (frame : Frame (SourceLabel carried result)) :
    Frame (Label saved carried result) :=
  carryFrameWith (.cons value .nil) frame

/-- The emitted entry and each block reproduce the source transfer, with
the same saved values prepended to the header arguments. -/
structure RoutesWith (source : Cfg TargetOp (SourceLabel carried result) Input [result])
    (target : Cfg TargetOp (Label saved carried result extra) Input [result])
    (input : Env Input) (values : Env (extra ++ [saved])) : Prop where
  entry :
    target.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      (source.entry.eval evalOp (fun term env => Terminator.eval env term) input).map
        (carryFrameWith values) id
  block : ∀ frame : Frame (SourceLabel carried result),
    let routed := carryFrameWith values frame
    (target.block routed.label).eval evalOp (fun term env => Terminator.eval env term)
      (routed.args.append input) =
      ((source.block frame.label).eval evalOp (fun term env => Terminator.eval env term)
        (frame.args.append input)).map (carryFrameWith values) id

structure Routes (source : Cfg TargetOp (SourceLabel carried result) Input [result])
    (target : Cfg TargetOp (Label saved carried result) Input [result])
    (input : Env Input) (value : BitVec saved.val) : Prop where
  entry :
    target.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      (source.entry.eval evalOp (fun term env => Terminator.eval env term) input).map (carryFrame value) id
  block : ∀ frame : Frame (SourceLabel carried result),
    let routed := carryFrame value frame
    (target.block routed.label).eval evalOp (fun term env => Terminator.eval env term)
      (routed.args.append input) =
      ((source.block frame.label).eval evalOp (fun term env => Terminator.eval env term)
        (frame.args.append input)).map (carryFrame value) id

/-- Rank the actual source cuts with the checked natural-loop depth. The
only supported destination is cut zero of the existing preheader. -/
def pickAndHoist? (g : Program Input carried result entrySigs headerSigs)
    (tree : DominatorTree (lower g)) : Option (Point (SourceLabel carried result) × Output Input carried result) :=
  match (lower g).block .header with
  | .terminator _ => none
  | .letOp (w := saved) op operands rest => do
    let cut ← LoopForest.choosePlacement tree blocks (operandSites operands) (useSites 0 1 rest)
    if cut.block.isNone && cut.cut == 0 then
      let captured ← capture? operands
      pure (cut, ⟨saved, emit (lower g).entry op captured rest⟩)
    else none

/-- An in-scope variable names either an immutable input or a local definition.
The local number is the cut after the defining binding, with zero for the latch. -/
abbrev Origins (Input Γ : List Width) := ∀ {w}, Var Γ w → Var Input w ⊕ Nat

def headerOrigins : Origins Input (carried :: Input)
  | _, .here => .inr 0
  | _, .there ref => .inl ref

def afterBinding (origins : Origins Input Γ) (cut : Nat) : Origins Input (w :: Γ)
  | _, .here => .inr cut
  | _, .there ref => origins ref

def originSites (origins : Origins Input Γ) : {args : List Width} →
    Operands Γ args → List (Point (SourceLabel carried result))
  | _, .nil => []
  | _, .cons ref rest =>
    let site := match origins ref with
      | .inl _ => ⟨none, 0⟩
      | .inr cut => ⟨headerId, cut⟩
    site :: originSites origins rest

/-- The captured variables denote the corresponding values in the entry environment. -/
def CapturesAgree (origins : Origins Input Γ) (env : Env Γ) (input : Env Input) : Prop :=
  ∀ {w} (ref : Var Γ w) (captured : Var Input w),
    origins ref = .inl captured → env.get ref = input.get captured

/-- Translate only directly captured operands, rejecting a read of any local result. -/
def captureOrigins? (origins : Origins Input Γ) :
    {args : List Width} → Operands Γ args → Option (Operands Input args)
  | _, .nil => some .nil
  | _, .cons ref rest =>
    match origins ref with
    | .inl input => (captureOrigins? origins rest).map (.cons input)
    | .inr _ => none

def replaceBinding (rename : Rename Γ Δ) (keep : Var Δ saved) : Rename (saved :: Γ) Δ
  | _, .here => keep
  | _, .there ref => rename ref

/-- A binding found in an existing typed block, with its sites and an emitter
for the block with that binding replaced by a reference to the saved value. -/
structure Binding (Input Γ : List Width) (saved carried result : Width) where
  args : List Width
  op : TargetOp args saved
  captured? : Option (Operands Input args)
  operands : List (Point (SourceLabel carried result))
  uses : List (Use (SourceLabel carried result))
  rewrite : ∀ {Δ : List Width}, Rename Γ Δ → Var Δ saved →
    Block TargetOp (Label saved carried result) Δ [result]

def Binding.prepend (op : TargetOp args w) (operands : Operands Γ args)
    (binding : Binding Input (w :: Γ) saved carried result) : Binding Input Γ saved carried result where
  args := binding.args
  op := binding.op
  captured? := binding.captured?
  operands := binding.operands
  uses := binding.uses
  rewrite rename keep := .letOp op (For.renameOperands rename operands)
    (binding.rewrite (under rename) (.there keep))

/-- Find a zero-based binding index and preserve the prefix in its original
order. Only the nominated let is removed. -/
def findBinding : (index cut : Nat) → {Γ : List Width} → Origins Input Γ →
    Block TargetOp (SourceLabel carried result) Γ [result] →
    Option ((saved : Width) × Binding Input Γ saved carried result)
  | _, _, _, _, .terminator _ => none
  | 0, cut, _, origins, .letOp (w := saved) op operands rest =>
    some ⟨saved, ⟨_, op, captureOrigins? origins operands, originSites origins operands,
      useSites 0 (cut + 1) rest, fun rename keep => routeCode (replaceBinding rename keep) keep rest⟩⟩
  | index + 1, cut, _, origins, .letOp op operands rest =>
    (findBinding index (cut + 1) (afterBinding origins (cut + 1)) rest).map
      fun ⟨saved, binding⟩ => ⟨saved, binding.prepend op operands⟩

/-- Apply the chooser's cut to the current entry and header code. The
emitted profile has the canonical exit that returns its sole argument. -/
def hoistCodeWith? (entry : Block TargetOp (SourceLabel carried result) Input [result])
    (header : Block TargetOp (SourceLabel carried result) (carried :: Input) [result]) (index : Nat)
    (choose : List (Point (SourceLabel carried result)) → List (Use (SourceLabel carried result)) →
      Option (Point (SourceLabel carried result))) :
    Option (Point (SourceLabel carried result) × Output Input carried result) := do
  let ⟨saved, binding⟩ ← findBinding index 0 headerOrigins header
  let cut ← choose binding.operands binding.uses
  if cut.block.isNone && cut.cut == 0 then
    let captured ← binding.captured?
    let rewritten := binding.rewrite Var.there .here
    pure (cut, ⟨saved, emitHeader entry binding.op captured rewritten⟩)
  else none

/-- Hoist on the native program's lowered entry and header. The caller
supplies the placement check through `choose`. -/
def hoistBindingWith? (g : Program Input carried result entrySigs headerSigs) (index : Nat)
    (choose : List (Point (SourceLabel carried result)) → List (Use (SourceLabel carried result)) →
      Option (Point (SourceLabel carried result))) :
    Option (Point (SourceLabel carried result) × Output Input carried result) :=
  hoistCodeWith? (lower g).entry ((lower g).block .header) index choose

/-- Hoist the nominated binding when its exact use sites and operand origins
lead the loop ranker to preheader cut zero and the operands are captured inputs. -/
def pickBindingAndHoist? (g : Program Input carried result entrySigs headerSigs)
    (tree : DominatorTree (lower g)) (index : Nat) :
    Option (Point (SourceLabel carried result) × Output Input carried result) :=
  hoistBindingWith? g index (LoopForest.choosePlacement tree blocks)

/-- At the consumer, the prerequisite is an input to the preheader's
second binding. Other local origins retain their original definition cuts. -/
def afterPrerequisite (origins : Origins Input Γ) : Origins (w :: Input) (w :: Γ)
  | _, .here => .inl .here
  | _, .there ref => (origins ref).map Var.there id

variable {prerequisite consumer : Width}

structure Slice (Input Γ : List Width) (prerequisite consumer carried result : Width) where
  prerequisiteArgs : List Width
  prerequisiteOp : TargetOp prerequisiteArgs prerequisite
  prerequisiteInputs : Operands Input prerequisiteArgs
  prerequisiteSites : List (Point (SourceLabel carried result))
  prerequisiteUses : List (Use (SourceLabel carried result))
  consumerArgs : List Width
  consumerOp : TargetOp consumerArgs consumer
  consumerInputs : Operands (prerequisite :: Input) consumerArgs
  consumerSites : List (Point (SourceLabel carried result))
  consumerUses : List (Use (SourceLabel carried result))
  rewrite : ∀ {Δ : List Width}, Rename Γ Δ → Var Δ consumer → Var Δ prerequisite →
    Block TargetOp (Label prerequisite carried result [consumer]) Δ [result]

def Slice.prepend (op : TargetOp args w) (operands : Operands Γ args)
    (slice : Slice Input (w :: Γ) prerequisite consumer carried result) :
    Slice Input Γ prerequisite consumer carried result :=
  { slice with
    rewrite := fun rename keepConsumer keepPrerequisite =>
      .letOp op (For.renameOperands rename operands)
        (slice.rewrite (under rename) (.there keepConsumer) (.there keepPrerequisite)) }

/-- The consumer with its captured inputs and a rewrite through the retained
bindings between it and the prerequisite. -/
structure SliceConsumer (Input Γ : List Width) (prerequisite consumer carried result : Width) where
  args : List Width
  op : TargetOp args consumer
  inputs : Operands (prerequisite :: Input) args
  sites : List (Point (SourceLabel carried result))
  uses : List (Use (SourceLabel carried result))
  rewrite : ∀ {Δ : List Width}, Rename Γ Δ → Var Δ consumer → Var Δ prerequisite →
    Block TargetOp (Label prerequisite carried result [consumer]) Δ [result]

def SliceConsumer.prepend (op : TargetOp args w) (operands : Operands Γ args)
    (binding : SliceConsumer Input (w :: Γ) prerequisite consumer carried result) :
    SliceConsumer Input Γ prerequisite consumer carried result :=
  { binding with
    rewrite := fun rename keepConsumer keepPrerequisite =>
      .letOp op (For.renameOperands rename operands)
        (binding.rewrite (under rename) (.there keepConsumer) (.there keepPrerequisite)) }

/-- Follow the selected prerequisite through the retained bindings. Their
results are local origins and never become available to the preheader. -/
def findSliceConsumer : (gap cut : Nat) → {Γ : List Width} → Var Γ prerequisite →
    Origins (prerequisite :: Input) Γ → Block TargetOp (SourceLabel carried result) Γ [result] →
    Option ((consumer : Width) × SliceConsumer Input Γ prerequisite consumer carried result)
  | _, _, _, _, _, .terminator _ => none
  | 0, cut, _, prerequisiteRef, origins, .letOp (w := consumer) op operands rest => do
    if (positions prerequisiteRef.index operands 0).isEmpty then none else
      let inputs ← captureOrigins? origins operands
      pure ⟨consumer, ⟨_, op, inputs, originSites origins operands, useSites 0 (cut + 1) rest,
        fun rename keepConsumer keepPrerequisite =>
          routeCodeWith (replaceBinding rename keepConsumer)
            (.cons keepConsumer (.cons keepPrerequisite .nil)) rest⟩⟩
  | gap + 1, cut, _, prerequisiteRef, origins, .letOp op operands rest =>
    (findSliceConsumer gap (cut + 1) (.there prerequisiteRef) (afterBinding origins (cut + 1)) rest).map
      (fun ⟨consumer, binding⟩ => ⟨consumer, binding.prepend op operands⟩)

/-- Locate the prerequisite by its zero-based index and the consumer by the
number of bindings kept between them. Scan all uses of the prerequisite,
including retained instructions and both successor occurrences. -/
def findSliceAcross : (index gap cut : Nat) → {Γ : List Width} → Origins Input Γ →
    Block TargetOp (SourceLabel carried result) Γ [result] →
    Option ((prerequisite : Width) × (consumer : Width) × Slice Input Γ prerequisite consumer carried result)
  | _, _, _, _, _, .terminator _ => none
  | 0, gap, cut, _, origins, .letOp (w := prerequisite) op operands rest => do
    let inputs ← captureOrigins? origins operands
    let ⟨consumer, binding⟩ ← findSliceConsumer gap (cut + 1) .here (afterPrerequisite origins) rest
    pure ⟨prerequisite, consumer, {
      prerequisiteArgs := _
      prerequisiteOp := op
      prerequisiteInputs := inputs
      prerequisiteSites := originSites origins operands
      prerequisiteUses := useSites 0 (cut + 1) rest
      consumerArgs := binding.args
      consumerOp := binding.op
      consumerInputs := binding.inputs
      consumerSites := binding.sites
      consumerUses := binding.uses
      rewrite := fun rename keepConsumer keepPrerequisite =>
        binding.rewrite (replaceBinding rename keepPrerequisite) keepConsumer keepPrerequisite }⟩
  | index + 1, gap, cut, _, origins, .letOp op operands rest =>
    (findSliceAcross index gap (cut + 1) (afterBinding origins (cut + 1)) rest).map
      (fun ⟨first, second, slice⟩ => ⟨first, second, slice.prepend op operands⟩)

/-- The adjacent pair is the case with no retained bindings in the gap. -/
def findSlice (index cut : Nat) (origins : Origins Input Γ)
    (code : Block TargetOp (SourceLabel carried result) Γ [result]) :
    Option ((prerequisite : Width) × (consumer : Width) × Slice Input Γ prerequisite consumer carried result) :=
  findSliceAcross index 0 cut origins code

structure SliceOutput (Input : List Width) (carried result : Width) where
  prerequisite : Width
  consumer : Width
  cfg : Cfg TargetOp (Label prerequisite carried result [consumer]) Input [result]

def emitSlice (entry : Block TargetOp (SourceLabel carried result) Input [result])
    (slice : Slice Input (carried :: Input) prerequisite consumer carried result) :
    SliceOutput Input carried result :=
  ⟨prerequisite, consumer, {
    entry := .letOp slice.prerequisiteOp slice.prerequisiteInputs
      (.letOp slice.consumerOp slice.consumerInputs
        (routeCodeWith (fun ref => .there (.there ref))
          (.cons .here (.cons (.there .here) .nil)) entry))
    block
      | .header => slice.rewrite (fun ref => .there (.there ref)) .here (.there .here)
      | .exit => .terminator (.ret (.cons .here .nil)) }⟩

/-- Rank both definitions at preheader cut zero. Entry evaluates them in
dependency order. The gap counts retained bindings between the pair. -/
def pickSliceAcrossAndHoist? (g : Program Input carried result entrySigs headerSigs)
    (tree : DominatorTree (lower g)) (prerequisiteIndex gap : Nat) :
    Option (SliceOutput Input carried result) := do
  let ⟨_, _, slice⟩ ← findSliceAcross prerequisiteIndex gap 0 headerOrigins ((lower g).block .header)
  let first ← LoopForest.choosePlacement tree blocks slice.prerequisiteSites slice.prerequisiteUses
  let second ← LoopForest.choosePlacement tree blocks slice.consumerSites slice.consumerUses
  if first.block.isNone && first.cut == 0 && second.block.isNone && second.cut == 0 then
    some (emitSlice (lower g).entry slice)
  else none

def pickSliceAndHoist? (g : Program Input carried result entrySigs headerSigs)
    (tree : DominatorTree (lower g)) (consumerIndex : Nat) :
    Option (SliceOutput Input carried result) :=
  match consumerIndex with
  | 0 => none
  | prerequisiteIndex + 1 => pickSliceAcrossAndHoist? g tree prerequisiteIndex 0

def Slice.savedValues (slice : Slice Input Γ prerequisite consumer carried result)
    (input : Env Input) : Env [consumer, prerequisite] :=
  let first := evalOp slice.prerequisiteOp (slice.prerequisiteInputs.eval input)
  let second := evalOp slice.consumerOp (slice.consumerInputs.eval (.cons first input))
  .cons second (.cons first .nil)


end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
