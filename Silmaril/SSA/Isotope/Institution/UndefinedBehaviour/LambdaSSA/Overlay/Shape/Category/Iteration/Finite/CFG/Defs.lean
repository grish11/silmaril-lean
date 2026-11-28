module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Defs

/-! # Typed packet-local overlay CFGs

All internal labels accept the same exact payload type. Blocks use their
incoming payload and a fixed capture, and have the acyclic syntax of the
finite step evaluator. An exact sum selects a return or an internal jump.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG

open Syntax

universe u

/-- The number of left alternatives is the number of internal labels.
The final empty alternative cannot carry a shaped value. -/
def Packet (A : Syntax.Ty) : Nat → Syntax.Ty
  | 0 => .empty
  | n + 1 => .coprod A (Packet A n)

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {Γ L : List Syntax.Ty} {X A B : Syntax.Ty}
variable {n states captures seeds results : Nat}

def pack : {n : Nat} → Fin n → Payload A → Payload (Packet A n)
  | 0, i, _ => i.elim0
  | _ + 1, i, a =>
    Fin.cases ⟨.inl a.val, .inl a.property⟩
      (fun j => let p := pack j a; ⟨.inr p.val, .inr p.property⟩) i

def unpack : {n : Nat} → Payload (Packet A n) → Fin n × Payload A
  | 0, a => (noEmptyPayload a).elim
  | _ + 1, a =>
    match splitPayload a with
    | .inl b => (0, b)
    | .inr tail =>
      let p := unpack tail
      (p.1.succ, p.2)

theorem unpack_pack (i : Fin n) (a : Payload A) : unpack (pack i a) = (i, a) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (let p := unpack (pack j a); (p.1.succ, p.2)) = _
      rw [ih]

theorem pack_unpack (a : Payload (Packet A n)) : pack (unpack a).1 (unpack a).2 = a := by
  induction n with
  | zero => exact (noEmptyPayload a).elim
  | succ n ih =>
    obtain ⟨_, typed⟩ := a
    cases typed with
    | inl => rfl
    | inr typed =>
      let tail : Payload (Packet A n) := ⟨_, typed⟩
      change (⟨.inr (pack (unpack tail).1 (unpack tail).2).val, .inr (pack (unpack tail).1 (unpack tail).2).property⟩ :
          Payload (Packet A (n + 1))) =
        ⟨.inr tail.val, .inr tail.property⟩
      exact Subtype.ext (congrArg (fun x : Payload (Packet A n) => Value.inr x.val) (ih tail))

def packetEquiv (A : Syntax.Ty) (n : Nat) : (Fin n × Payload A) ≃ Payload (Packet A n) where
  toFun p := pack p.1 p.2
  invFun := unpack
  left_inv p := unpack_pack p.1 p.2
  right_inv := pack_unpack

/-- The CFG codebook uses the original seed and result values. The finite
label index is added to every seed code before exact-sum iteration. -/
def packedCodes (n : Nat) (codes : Codes X A B captures seeds results) :
    Codes X (Packet A n) B captures (n * seeds) results where
  capture := codes.capture
  seed := finProdFinEquiv.symm.trans (((Equiv.refl (Fin n)).prodCongr codes.seed).trans (packetEquiv A n))
  result := codes.result

/-- A finite table of acyclic blocks. The initial jump is supplied when
building the CFG. Each block observes the same single capture value. -/
structure Blocks (Φ : Type u) [HasTy Φ Syntax.Ty] (X A B : Syntax.Ty) (n : Nat) where
  block : Fin n → Program Φ [A, X] (.coprod B (Packet A n))

abbrev labels (A : Syntax.Ty) (n : Nat) := List.replicate n A

def label (i : Fin n) : Fin (labels A n).length :=
  i.cast List.length_replicate.symm

def blockIndex (i : Fin (labels A n).length) : Fin n :=
  i.cast List.length_replicate

theorem label_type (i : Fin (labels A n).length) : (labels A n).get i = A := by
  simp

theorem internal_type (i : Fin n) :
    (labels A n ++ [B]).get (Feedback.internal (labels A n) [B] (label i)) = A := by
  simp [Feedback.internal, label, List.get_eq_getElem, List.getElem_append_left]

def exitLabel (A B : Syntax.Ty) (n : Nat) : Fin (labels A n ++ [B]).length :=
  ((0 : Fin 1).natAdd (labels A n).length).cast List.length_append.symm

theorem external_type : (labels A n ++ [B]).get (exitLabel A B n) = B := by
  simp [exitLabel, List.get_eq_getElem, List.getElem_append_right]

/-- A native branch whose constructor expression is checked against the
chosen positional label. -/
def jump (i : Fin L.length) (type : L.get i = A) (a : Expr Γ A) : Region Φ Γ L :=
  .native ⟨.br i a.term, .br (type ▸ List.getElem?_eq_getElem i.isLt) a.typed⟩

/-- Bind the unique exit of a singleton region. -/
def bindOne (r : Region Φ Γ [A]) (k : Region Φ (A :: Γ) L) : Region Φ Γ L :=
  .lsubst r (fun i => by obtain rfl := Fin.eq_zero i; exact k)

/-- Route an exact sum using the native case dispatcher. Only the chosen
payload is passed to its label continuation. -/
def select (left : Region Φ (A :: .coprod A B :: Γ) L)
    (right : Region Φ (B :: .coprod A B :: Γ) L) :
    Region Φ (.coprod A B :: Γ) L :=
  .lsubst (.native (Program.caseRegion (.var 0)))
    (Fin.cases (motive := fun i => Region Φ ([A, B].get i :: .coprod A B :: Γ) L)
      (by exact left)
      (fun i => by obtain rfl := Fin.eq_zero i; exact right))

/-- Decode a packet into a positional jump. The last alternative uses native
empty elimination, since a shaped value cannot select it. -/
def routePacket (fallback : Fin L.length) :
    {k : Nat} → {Γ : List Syntax.Ty} → (target : Fin k → Fin L.length) →
      (∀ j, L.get (target j) = A) → Region Φ (Packet A k :: Γ) L
  | 0, _, _, _ => .native ⟨.br fallback (.abort (.var 0)),
      .br (List.getElem?_eq_getElem fallback.isLt) (.abort (.var (i := 0) rfl))⟩
  | _ + 1, _, target, typed =>
    select (jump (target 0) (typed 0) (.var 0))
      (routePacket fallback (fun j => target j.succ) (fun j => typed j.succ))

def route (A B : Syntax.Ty) (n : Nat) {Γ : List Syntax.Ty} :
    Region Φ (.coprod B (Packet A n) :: Γ) (labels A n ++ [B]) :=
  select (jump (exitLabel A B n) external_type (.var 0))
    (routePacket (exitLabel A B n) (fun i => Feedback.internal (labels A n) [B] (label i))
      internal_type)

/-- Decode a code as an actual positional CFG invocation. -/
def invocation (codes : Codes X A B captures seeds results) (prim : Primitives Φ states) :
    Fin ((n * seeds) * states) → Fin (labels A n).length × Value Unit × Fin states :=
  fun p =>
    let input := ((packedCodes n codes).carrier prim).invocation p
    let decoded := unpack input.1
    (label decoded.1, decoded.2.val, input.2)

/-- Encode a chosen label, typed incoming payload and machine state. -/
def encode (codes : Codes X A B captures seeds results) (i : Fin n) (a : Payload A) (s : Fin states) :
    Fin ((n * seeds) * states) :=
  finProdFinEquiv ((packedCodes n codes).seed.symm (pack i a), s)

def castHead {A' : Syntax.Ty} (h : A' = A) (r : Region Φ (A :: Γ) L) : Region Φ (A' :: Γ) L :=
  h.symm ▸ r

namespace Blocks

/-- The block computes its exact tag, then native case and branch atoms
send its reply to the positional internal label or the external exit. -/
def routed (cfg : Blocks Φ X A B n) (i : Fin (labels A n).length) :
    Region Φ ((labels A n).get i :: [X]) (labels A n ++ [B]) :=
  castHead (label_type i) (bindOne (cfg.block (blockIndex i)).region (route A B n))

/-- Actual typed overlay feedback over the original positional internal labels.
The entry is a single native jump with a constructor expression. -/
def region (cfg : Blocks Φ X A B n) (start : Fin n) (input : Expr [X] A) : Region Φ [X] [B] :=
  .feedback
    (jump (Feedback.internal (labels A n) [B] (label start)) (internal_type start) input)
    cfg.routed

/-- The exact-sum step selects a typed block by decoding the incoming packet.
Its complete observation uses the actual shaped evaluator of that block. -/
noncomputable def step (cfg : Blocks Φ X A B n) (prim : Primitives Φ states) (c : Payload X) :
    Arrow (single (σ := Fin states) (atomType := atomType) (Packet A n))
      (single (.coprod B (Packet A n))) where
  run _ p s :=
    let decoded := unpack (payloadAtZero p)
    Shape.denote (cfg.block decoded.1).region (model prim ((emptyBindings.push c).push decoded.2)) s
  returnsTyped _ p s := by
    let decoded := unpack (payloadAtZero p)
    exact Shape.returns_typed (cfg.block decoded.1).region
      (model prim ((emptyBindings.push c).push decoded.2)) s

/-- Evaluate exactly the block named by the invocation. Its repeat tag
is encoded as another invocation, with the returned machine state. -/
def generate (cfg : Blocks Φ X A B n) (codes : Codes X A B captures seeds results)
    (prim : Primitives Φ states) : Table captures ((n * seeds) * states) results states :=
  fun c p =>
    let packed := packedCodes n codes
    let input := (packed.carrier prim).invocation p
    let decoded := unpack input.1
    ((cfg.block decoded.1).eval prim ((emptyBindings.push (codes.capture c)).push decoded.2) input.2).row packed

end Blocks

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG
