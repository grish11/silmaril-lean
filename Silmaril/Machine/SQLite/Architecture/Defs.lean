module

/-!
# SQLite architecture diagram

The inventory transcribes the labeled boxes and arrows in the pinned
[SQLite architecture diagram](https://www.sqlite.org/arch.html).
See `docs/projects/sqlite-track-e/architecture.md` for the pin and the scope
of the modeled edges.
-/

@[expose] public section

namespace Silmaril.Machine.SQLite.Architecture

inductive Node where
  | core | backend | compiler | accessories
  | interface | commandProcessor | virtualMachine
  | btree | pager | osInterface
  | tokenizer | parser | codeGenerator
  | utilities | testCode
  deriving DecidableEq, Repr

def nodes : List Node :=
  [.core, .backend, .compiler, .accessories,
   .interface, .commandProcessor, .virtualMachine, .btree, .pager, .osInterface,
   .tokenizer, .parser, .codeGenerator, .utilities, .testCode]

/-- The SVG text elements for each box, preserving line breaks and nonbreaking spaces. -/
def labelLines : Node → List String
  | .core => ["Core"]
  | .backend => ["Backend"]
  | .compiler => ["SQL\u00a0Compiler"]
  | .accessories => ["Accessories"]
  | .interface => ["Interface"]
  | .commandProcessor => ["SQL\u00a0Command", "Processor"]
  | .virtualMachine => ["Virtual\u00a0Machine"]
  | .btree => ["B-Tree"]
  | .pager => ["Pager"]
  | .osInterface => ["OS\u00a0Interface"]
  | .tokenizer => ["Tokenizer"]
  | .parser => ["Parser"]
  | .codeGenerator => ["Code", "Generator"]
  | .utilities => ["Utilities"]
  | .testCode => ["Test\u00a0Code"]

/-- The box caption on one line, using ordinary spaces. -/
def label (node : Node) : String :=
  let chars := List.intercalate [' '] ((labelLines node).map String.toList)
  String.ofList (chars.map fun c => if c == '\u00a0' then ' ' else c)

def parent : Node → Option Node
  | .core | .backend | .compiler | .accessories => none
  | .interface | .commandProcessor | .virtualMachine => some .core
  | .btree | .pager | .osInterface => some .backend
  | .tokenizer | .parser | .codeGenerator => some .compiler
  | .utilities | .testCode => some .accessories

/-- The diagram's grouping colors, as RGB triples. The eleven leaf boxes are white. -/
def fill : Node → Nat × Nat × Nat
  | .core => (216, 236, 208)
  | .backend => (208, 236, 232)
  | .compiler => (232, 216, 208)
  | .accessories => (224, 236, 200)
  | _ => (255, 255, 255)

/-- Flattened immediate containment, oriented from group to member. -/
def containment : List (Node × Node) :=
  nodes.filterMap fun child => (parent child).map fun group => (group, child)

/-- The nine drawn arrows, oriented from tail to arrowhead. -/
def diagramArrows : List (Node × Node) :=
  [(.interface, .commandProcessor), (.commandProcessor, .virtualMachine),
   (.virtualMachine, .btree), (.btree, .pager), (.pager, .osInterface),
   (.tokenizer, .parser), (.parser, .codeGenerator),
   (.commandProcessor, .tokenizer), (.codeGenerator, .commandProcessor)]

/-- Modeled invocations, oriented from caller to callee. The code generator hands
bytecode back to the command processor. The step interface also invokes the VM. -/
def calls : List (Node × Node) :=
  diagramArrows.filter (· ≠ (.codeGenerator, .commandProcessor)) ++
    [(.interface, .virtualMachine)]

/-- Selected semantic contracts, oriented from consumer to provider.
These dependencies can run in a different direction from an invocation. -/
def dependencies : List (Node × Node) :=
  [(.interface, .commandProcessor), (.interface, .virtualMachine), (.interface, .utilities),
   (.commandProcessor, .tokenizer), (.commandProcessor, .codeGenerator),
   (.tokenizer, .parser), (.parser, .utilities),
   (.codeGenerator, .parser), (.codeGenerator, .virtualMachine),
   (.virtualMachine, .btree), (.btree, .pager), (.pager, .osInterface),
   (.testCode, .interface)]

end Silmaril.Machine.SQLite.Architecture
