module

public import Silmaril.SSA.RVSDG.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs

/-! # A typed straight-line λSSA ↔ RVSDG fragment

An expression returns a variable or binds the result of a unary instruction
applied to a variable. All RVSDG argument and result ports are value ports.
Each instruction produces a singleton result and the let sequence fixes the
local numbering. SSA types and opcodes are carried without erasure.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open Silmaril.Isotope.LambdaSSA (At Tm)

universe u v
variable {τ : Type u} {Φ : Type v} [HasTy Φ τ]

abbrev Ty (τ : Type u) := PortType τ PEmpty

def inputs (Γ : List τ) : Ports (Ty τ) := Γ.map .value

/-- An instruction's ordered port signatures are determined by its λSSA signature. -/
inductive Opcode (Φ : Type v) [HasTy Φ τ] : Dialect τ PEmpty where
  | instr (f : Φ) : Opcode Φ [.value (instrSrc f)] [.value (instrTrg f)]

def index {Γ : List τ} {A : τ} : Port Γ A → Nat
  | .head => 0
  | .tail p => index p + 1

theorem index_at {Γ : List τ} {A : τ} (p : Port Γ A) : At Γ (index p) A := by
  induction p with
  | head => rfl
  | tail p ih => exact ih

def inputPort {Γ : List τ} {A : τ} : Port Γ A → Port (inputs Γ) (.value A)
  | .head => .head
  | .tail p => .tail (inputPort p)

def priorIndex (out : Ports (Ty τ)) :
    (past : List (Ports (Ty τ))) → Fin past.length → Fin (past ++ [out]).length
  | [], i => i.elim0
  | _ :: tail, i => Fin.cases ⟨0, Nat.zero_lt_succ _⟩ (fun j => (priorIndex out tail j).succ) i

def priorPort (out : Ports (Ty τ)) {t : Ty τ} :
    (past : List (Ports (Ty τ))) → (i : Fin past.length) →
    Port past[i] t → Port (past ++ [out])[priorIndex out past i] t
  | [], i => i.elim0
  | head :: tail, i => Fin.cases
      (motive := fun j => Port (head :: tail)[j] t →
        Port ((head :: tail) ++ [out])[priorIndex out (head :: tail) j] t)
      id (fun j => priorPort out tail j) i

/-- Existing local addresses retain their node number when a result is appended. -/
def keepOrigin {args : Ports (Ty τ)} {past : List (Ports (Ty τ))} {t : Ty τ}
    (out : Ports (Ty τ)) : Origin args past t → Origin args (past ++ [out]) t
  | .arg p => .arg p
  | .output i p => .output (priorIndex out past i) (priorPort out past i p)

def lastIndex (out : Ports (Ty τ)) :
    (past : List (Ports (Ty τ))) → Fin (past ++ [out]).length
  | [] => ⟨0, Nat.zero_lt_succ _⟩
  | _ :: tail => (lastIndex out tail).succ

def lastPort {out : Ports (Ty τ)} {t : Ty τ} (p : Port out t) :
    (past : List (Ports (Ty τ))) → Port (past ++ [out])[lastIndex out past] t
  | [] => p
  | _ :: tail => lastPort p tail

/-- Address the variable just bound, at the end of the numbered prefix. -/
def newOrigin (args : Ports (Ty τ)) (past : List (Ports (Ty τ))) (A : τ) :
    Origin args (past ++ [[.value A]]) (.value A) :=
  .output (lastIndex [.value A] past) (lastPort .head past)

/-- The root's input order is the SSA de Bruijn order. Each SSA binder adds a
new index zero, while the matching RVSDG vertex gets the next number. -/
inductive Scope (root : List τ) : List (Ports (Ty τ)) → List τ → Type u where
  | initial : Scope root [] root
  | bind {past : List (Ports (Ty τ))} {Γ : List τ} (s : Scope root past Γ) (A : τ) :
      Scope root (past ++ [[.value A]]) (A :: Γ)

def Scope.origin {root : List τ} : {past : List (Ports (Ty τ))} → {Γ : List τ} →
    Scope root past Γ → {A : τ} → Port Γ A → Origin (inputs root) past (.value A)
  | _, _, .initial, _, p => .arg (inputPort p)
  | _, _, .bind _ A, _, .head => newOrigin _ _ A
  | _, _, .bind s _, _, .tail p => keepOrigin _ (s.origin p)

variable {root Γ : List τ} {past sigs : List (Ports (Ty τ))} {A : τ}

def node (s : Scope root past Γ) (f : Φ) (p : Port Γ (instrSrc f)) :
    Node (Opcode Φ) (inputs root) past [.value (instrTrg f)] :=
  ⟨[.value (instrSrc f)], .simple (.instr f), .cons (s.origin p) .nil, fun i => i.elim0⟩

/-- Syntactic correspondence at a typed open scope. The rule for a binder
preserves the opcode, the input origin and the order of the continuation. -/
inductive Related : {past : List (Ports (Ty τ))} → {Γ : List τ} → Scope root past Γ →
    {sigs : List (Ports (Ty τ))} → Tm Φ → Term (Opcode Φ) (inputs root) past sigs [.value A] →
    Type (max u v) where
  | ret {past : List (Ports (Ty τ))} {Γ : List τ} {s : Scope root past Γ} (p : Port Γ A) :
      Related s (.var (index p)) (.ret (.cons (s.origin p) .nil))
  | bind {past : List (Ports (Ty τ))} {Γ : List τ} {s : Scope root past Γ}
      {sigs : List (Ports (Ty τ))} (f : Φ) (p : Port Γ (instrSrc f)) {body : Tm Φ}
      {rest : Term (Opcode Φ) (inputs root) (past ++ [[.value (instrTrg f)]]) sigs [.value A]} :
      Related (s.bind (instrTrg f)) body rest →
      Related s (.let₁ (.op f (.var (index p))) body)
        (.bind (node s f p) (fun i => i.elim0) rest)

/-- Every relation witness supplies exact typing in the repository's λSSA. -/
theorem Related.typing [TypeFormers τ] {s : Scope root past Γ} {t : Tm Φ}
    {rv : Term (Opcode Φ) (inputs root) past sigs [.value A]} (rel : Related s t rv) :
    Tm.HasType Γ t A := by
  induction rel with
  | ret p => exact .var (index_at p)
  | bind f p rel ih => exact .let₁ (.op (.var (index_at p))) ih

/-- Admission on the actual λSSA expression, independently of RVSDG syntax. -/
inductive SSAForm : (Γ : List τ) → Tm Φ → τ → Type (max u v) where
  | ret {Γ : List τ} {A : τ} (p : Port Γ A) : SSAForm Γ (.var (index p)) A
  | bind {Γ : List τ} {body : Tm Φ} {A : τ} (f : Φ) (p : Port Γ (instrSrc f)) :
      SSAForm (instrTrg f :: Γ) body A → SSAForm Γ (.let₁ (.op f (.var (index p))) body) A

/-- Admission on the actual RVSDG let sequence. It certifies that each
user wire points at the port of a live argument or singleton primitive vertex. -/
inductive RVForm : {past : List (Ports (Ty τ))} → {Γ : List τ} → Scope root past Γ →
    {sigs : List (Ports (Ty τ))} → Term (Opcode Φ) (inputs root) past sigs [.value A] →
    Type (max u v) where
  | ret {past : List (Ports (Ty τ))} {Γ : List τ} {s : Scope root past Γ}
      (p : Port Γ A) : RVForm s (.ret (.cons (s.origin p) .nil))
  | bind {past : List (Ports (Ty τ))} {Γ : List τ} {s : Scope root past Γ}
      {sigs : List (Ports (Ty τ))} (f : Φ) (p : Port Γ (instrSrc f))
      {rest : Term (Opcode Φ) (inputs root) (past ++ [[.value (instrTrg f)]]) sigs [.value A]} :
      RVForm (s.bind (instrTrg f)) rest → RVForm s (.bind (node s f p) (fun i => i.elim0) rest)

/-- Construct the RVSDG member of the fibre of an admitted λSSA expression. -/
def lower : {past : List (Ports (Ty τ))} → {Γ : List τ} → (s : Scope root past Γ) →
    {t : Tm Φ} → SSAForm Γ t A →
    Σ sigs, Σ rv : Term (Opcode Φ) (inputs root) past sigs [.value A], Related s t rv
  | _, _, s, _, .ret p => ⟨[], .ret (.cons (s.origin p) .nil), .ret p⟩
  | _, _, s, _, .bind f p rest =>
    let ⟨tail, rv, rel⟩ := lower (s.bind (instrTrg f)) rest
    ⟨[.value (instrTrg f)] :: tail, .bind (node s f p) (fun i => i.elim0) rv, .bind f p rel⟩

/-- Construct the λSSA member of the fibre of an admitted RVSDG term. -/
def raise : {past sigs : List (Ports (Ty τ))} → {Γ : List τ} → {s : Scope root past Γ} →
    {rv : Term (Opcode Φ) (inputs root) past sigs [.value A]} → RVForm s rv →
    Σ t : Tm Φ, Related s t rv
  | _, _, _, _, _, .ret p => ⟨.var (index p), .ret p⟩
  | _, _, _, _, _, .bind f p rest =>
    let ⟨t, rel⟩ := raise rest
    ⟨.let₁ (.op f (.var (index p))) t, .bind f p rel⟩

/-- Admit a numbered table through its checked linearization. -/
abbrev GraphForm (g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]) :=
  RVForm (Scope.initial (root := Γ)) g.toTerm

/-- Correspondence with a numbered graph uses its typed linearization. -/
abbrev GraphRelated (t : Tm Φ) (g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]) :=
  Related (Scope.initial (root := Γ)) t g.toTerm

def raiseGraph (g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]) (h : GraphForm g) :
    Σ t : Tm Φ, GraphRelated t g :=
  raise h

end Silmaril.SSA.RVSDG.LambdaSSA
