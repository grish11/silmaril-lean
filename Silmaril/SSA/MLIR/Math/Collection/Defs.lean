module

/-! # Typed collections of scalar mathematical operations

An operation has an exact reference on an explicit domain and may also have a
local executable model. A backend can be related to the reference with its own
input decoding and output observation. An observation states a policy and can
be used without asserting that any backend satisfies it.
-/

@[expose] public section

namespace Silmaril.MLIR.MathCollection

/-- The exact and encoded carriers of a value sort. -/
structure ValueSort where
  exact : Type
  encoded : Type

/-- An ordered pair of operands. -/
abbrev ValueSort.pair (a b : ValueSort) : ValueSort where
  exact := a.exact × b.exact
  encoded := a.encoded × b.encoded

structure Reference (α β : Type) where
  domain : α → Prop
  value : (x : α) → domain x → β

def Reference.total {α β : Type} (f : α → β) : Reference α β where
  domain _ := True
  value x _ := f x

/-- The graph of a reference, including its domain condition. -/
def Reference.Holds {α β : Type} (ref : Reference α β) (x : α) (y : β) : Prop :=
  ∃ h : ref.domain x, ref.value x h = y

structure Operation (a b : ValueSort) where
  reference : Reference a.exact b.exact
  executable : Option (a.encoded → b.encoded)

/-- Interpret a family of symbols with typed operand and result carriers. -/
abbrev Collection (Symbol : ValueSort → ValueSort → Type) :=
  ∀ {a b}, Symbol a b → Operation a b

/-- The result graph of the local evaluator. -/
def Operation.Executes {a b : ValueSort} (op : Operation a b)
    (input : a.encoded) (output : b.encoded) : Prop :=
  op.executable.map (fun run => run input) = some output

/-- The reference domain is checked after decoding. The output policy can
inspect the encoded operand, for example when a zero's sign matters. -/
structure Observation (a b : ValueSort) where
  decodeInput : a.encoded → Option a.exact
  acceptOutput : a.encoded → b.exact → b.encoded → Prop

/-- Exact equality of decoded results. This policy compares only the decoded values. -/
def Observation.exact {a b : ValueSort} (decodeInput : a.encoded → Option a.exact)
    (decodeOutput : b.encoded → Option b.exact) : Observation a b where
  decodeInput := decodeInput
  acceptOutput _ value output := decodeOutput output = some value

def Operation.Accepts {a b : ValueSort} (op : Operation a b) (obs : Observation a b)
    (input : a.encoded) (output : b.encoded) : Prop :=
  ∃ x y, obs.decodeInput input = some x ∧ op.reference.Holds x y ∧
    obs.acceptOutput input y output

/-- On admitted encoded inputs, the backend has a result and every result in
its relation satisfies the policy. The caller supplies the backend's result
relation. A value-only relation observes only the results it reports. -/
def Operation.RealizesOn {a b : ValueSort} (op : Operation a b) (obs : Observation a b)
    (admit : a.encoded → Prop) (returns : a.encoded → b.encoded → Prop) : Prop :=
  ∀ input, admit input → (∃ output, returns input output) ∧
    ∀ output, returns input output → op.Accepts obs input output

end Silmaril.MLIR.MathCollection
