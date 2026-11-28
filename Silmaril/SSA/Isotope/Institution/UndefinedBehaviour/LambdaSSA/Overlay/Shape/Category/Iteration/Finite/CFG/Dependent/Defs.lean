module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Thms

/-! # Exact packets for heterogeneous positional overlay CFGs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent

open Syntax
open Silmaril.Isotope.LambdaSSA.Region (packedExitType packedExitValue)

universe u w x

variable {Γ R L : List Syntax.Ty}

variable {X : Syntax.Ty} {captures seeds results states : Nat}
variable {Φ : Type u} [HasTy Φ Syntax.Ty]

/-- Coded captures select the comparison scope. Seed and result codes cover
all exact packets of the respective ordered interfaces. -/
structure Codes (X : Syntax.Ty) (R L : List Syntax.Ty) (captures seeds results : Nat) where
  capture : Fin captures → Payload X
  seed : Fin seeds ≃ Packet R
  result : Fin results ≃ Packet L

def Codes.packed (C : Codes X R L captures seeds results) :
    Syntax.Codes X (packedExitType R) (packedExitType L) captures seeds results where
  capture := C.capture
  seed := C.seed.trans (packetEquiv R)
  result := C.result.trans (packetEquiv L)

def Codes.invocation (C : Codes X R L captures seeds results) :
    Fin (seeds * states) ≃ (Packet R × Fin states) :=
  finProdFinEquiv.symm.trans (C.seed.prodCongr (Equiv.refl _))

def Codes.carrier (C : Codes X R L captures seeds results) :
    PositionalCarrier R L Unit (Fin states) (seeds * states) results states where
  invocation p :=
    let input := C.invocation p
    (input.1.raw.1, input.1.raw.2, input.2)
  result := C.result.toEmbedding.trans Packet.erase
  final := Function.Embedding.refl _

/-- Pack the ordered return label into the exact SSA tag, preserving the
machine state and leaving the other observations as they are. -/
def packOutcome {α : Type w} {σ : Type x} : Outcome L.length α σ → Outcome 1 α σ
  | .ret i a s => .ret 0 (packedExitValue i a) s
  | .fault s => .fault s
  | .diverge => .diverge

def packBehaviour {α : Type w} {σ : Type x} (behaviour : Behaviour L.length α σ) : Behaviour 1 α σ :=
  behaviour.map (Set.image (packOutcome (L := L)))

theorem internal_type (i : Fin R.length) : (R ++ L).get (Feedback.internal R L i) = R.get i := by
  simp [Feedback.internal, List.get_eq_getElem, List.getElem_append_left]

def exitLabel (R L : List Syntax.Ty) (i : Fin L.length) : Fin (R ++ L).length :=
  (i.natAdd R.length).cast List.length_append.symm

theorem external_type (i : Fin L.length) : (R ++ L).get (exitLabel R L i) = L.get i := by
  simp [exitLabel, List.get_eq_getElem, List.getElem_append_right]

/-- An empty packet cannot reach this native empty elimination. Its local
empty-typed label makes the term well typed even with no external labels. -/
def emptyRoute : Region Φ (.empty :: Γ) L :=
  .native ⟨LambdaSSA.Region.unpackExits ([] : List Syntax.Ty),
    .cfg (fun _ : Fin 1 => .empty)
      (.br (ℓ := 0) rfl (.var (i := 0) rfl))
      (fun _ => .br (ℓ := 0) rfl (.var (i := 0) rfl))⟩

/-- Dispatch through the installed native case and branch atoms, reusing
the packet shape of the source interface and the supplied positional map. -/
def routePacket : {P Γ : List Syntax.Ty} → (target : Fin P.length → Fin L.length) →
    (∀ j, L.get (target j) = P.get j) → Region Φ (packedExitType P :: Γ) L
  | [], _, _, _ => emptyRoute
  | _ :: _, _, target, typed =>
    CFG.select (CFG.jump (target 0) (typed 0) (.var 0))
      (routePacket (fun j => target j.succ) (fun j => typed j.succ))

/-- Run a native request and route its packed reply to the supplied labels. -/
def packedRequestTo (f : Φ) (arg : Expr Γ (instrSrc f)) (reply : instrTrg f = packedExitType R)
    (target : Fin R.length → Fin L.length) (typed : ∀ i, L.get (target i) = R.get i) :
    Region Φ Γ L :=
  CFG.bindOne (.native (Program.requestRegion f arg))
    (CFG.castHead reply (routePacket target typed))

/-- Dispatch to the exact positional reply interface. -/
def packedRequest (f : Φ) (arg : Expr Γ (instrSrc f)) (typed : instrTrg f = packedExitType R) :
    Region Φ Γ R :=
  packedRequestTo f arg typed id (fun _ => rfl)

def route (R L : List Syntax.Ty) {Γ : List Syntax.Ty} :
    Region Φ (.coprod (packedExitType L) (packedExitType R) :: Γ) (R ++ L) :=
  CFG.select (routePacket (exitLabel R L) external_type)
    (routePacket (Feedback.internal R L) internal_type)

/-- A block receives the exact type of its own label and the fixed capture.
Returns and internal jumps select their respective ordered packet interfaces. -/
structure Blocks (Φ : Type u) [HasTy Φ Syntax.Ty] (X : Syntax.Ty) (R L : List Syntax.Ty) where
  block : (i : Fin R.length) → Program Φ [R.get i, X] (.coprod (packedExitType L) (packedExitType R))

namespace Blocks

def routed (g : Blocks Φ X R L) (i : Fin R.length) :
    Region Φ (R.get i :: [X]) (R ++ L) :=
  CFG.bindOne (g.block i).region (route R L)

/-- The checked representative is the existing positional overlay CFG. -/
def region (g : Blocks Φ X R L) (i : Fin R.length) (input : Expr [X] (R.get i)) : Region Φ [X] L :=
  .feedback (CFG.jump (Feedback.internal R L i) (internal_type i) input) g.routed

/-- Compute rows from syntax, indexing repeats by a typed packet and the
machine state returned by the block. -/
def generate (g : Blocks Φ X R L) (C : Codes X R L captures seeds results)
    (prim : Primitives Φ states) : Table captures (seeds * states) results states :=
  fun c p =>
    let input := C.invocation p
    ((g.block input.1.1).eval prim ((emptyBindings.push (C.capture c)).push input.1.2) input.2).row C.packed

/-- The packed dispatcher uses the same typed block denotations. -/
noncomputable def step (g : Blocks Φ X R L) (prim : Primitives Φ states) (c : Payload X) :
    Arrow (single (σ := Fin states) (atomType := atomType) (packedExitType R))
      (single (.coprod (packedExitType L) (packedExitType R))) where
  run _ p s :=
    let input := unpack (payloadAtZero p)
    Shape.denote (g.block input.1).region (model prim ((emptyBindings.push c).push input.2)) s
  returnsTyped _ p s := by
    let input := unpack (payloadAtZero p)
    exact Shape.returns_typed (g.block input.1).region (model prim ((emptyBindings.push c).push input.2)) s

end Blocks

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
