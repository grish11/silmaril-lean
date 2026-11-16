module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Syntax.Defs

-- Configurable builtin names intentionally have a canonical fallback instance.
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
variable [sorts : SortBindings]

/-- Freshness is computed from all original declared names, not assumed. -/
def declaredName : Kore.Modules.Declaration RawPattern Aliases.Declaration → Option String
  | .sort n | .hookedSort n _ => some n
  | .symbol d | .hookedSymbol d _ => some d.name
  | .alias d => some d.symbol.name
  | _ => none

def freshPrefix (d : Aliases.SourceDefinition) : String :=
  "BuiltinDomainValue" ++ String.ofList (List.replicate
    ((d.modules.flatMap (fun m => m.declarations.filterMap (fun d => declaredName d.declaration))).foldl
      (fun n name => max n name.toList.length) 0 + 1) 'x')

/-- Exposed decimal printing keeps the generated finite names kernel-reducible.
Decimal digits keep generated names short rather than using unary encoding. -/
def decimalPrint (n : Nat) : String :=
  if n < 10 then String.ofList [Char.ofNat ('0'.toNat + n)]
  else decimalPrint (n / 10) ++ String.ofList [Char.ofNat ('0'.toNat + n % 10)]
termination_by n
decreasing_by omega

def integerPrint : Int → String
  | .ofNat n => decimalPrint n
  | .negSucc n => "-" ++ decimalPrint (n + 1)

def literalName (literalPrefix : String) (moduleIndex : Nat) : Literal → String
  | .integer n => literalPrefix ++ "Module" ++ decimalPrint moduleIndex ++ "Int" ++ integerPrint n
  | .boolean b => literalPrefix ++ "Module" ++ decimalPrint moduleIndex ++ (if b then "BoolTrue" else "BoolFalse")

def literalDeclaration (literalPrefix : String) (moduleIndex : Nat) (l : Literal) : Kore.Modules.SymbolDeclaration :=
  ⟨literalName literalPrefix moduleIndex l, [], l.sort⟩

/-- The skeleton is only a visibility/type check of the original declarations:
replacing domain values with top cannot grant permission to use generated names.
The semantic lowering separately emits literal operations below. -/
def lowerPattern (literalPrefix : String) (moduleIndex : Nat) (skeleton : Bool) :
    Nat → RawPattern → Option (RawPattern × List Literal)
  | 0, _ => none
  | _ + 1, .domainValue s text => do
      let l ← Literal.parse s text
      return (if skeleton then .top s else .app (literalName literalPrefix moduleIndex l) [], [l])
  | _ + 1, .evar n s => some (.evar n s, [])
  | _ + 1, .svar n s => some (.svar n s, [])
  | _ + 1, .top s => some (.top s, [])
  | _ + 1, .bottom s => some (.bottom s, [])
  | n + 1, .app name args => do
      let ps ← args.mapM (lowerPattern literalPrefix moduleIndex skeleton n)
      return (.app name (ps.map Prod.fst), ps.flatMap Prod.snd)
  | n + 1, .neg s p => do
      let (p, ls) ← lowerPattern literalPrefix moduleIndex skeleton n p
      return (.neg s p, ls)
  | n + 1, .conj s p q => do
      let (p, ls) ← lowerPattern literalPrefix moduleIndex skeleton n p
      let (q, rs) ← lowerPattern literalPrefix moduleIndex skeleton n q
      return (.conj s p q, ls ++ rs)
  | n + 1, .disj s p q => do
      let (p, ls) ← lowerPattern literalPrefix moduleIndex skeleton n p
      let (q, rs) ← lowerPattern literalPrefix moduleIndex skeleton n q
      return (.disj s p q, ls ++ rs)
  | n + 1, .ex s name b p => do
      let (p, ls) ← lowerPattern literalPrefix moduleIndex skeleton n p
      return (.ex s name b p, ls)
  | n + 1, .all s name b p => do
      let (p, ls) ← lowerPattern literalPrefix moduleIndex skeleton n p
      return (.all s name b p, ls)
  | n + 1, .mu name s p => do
      let (p, ls) ← lowerPattern literalPrefix moduleIndex skeleton n p
      return (.mu name s p, ls)
  | n + 1, .nu name s p => do
      let (p, ls) ← lowerPattern literalPrefix moduleIndex skeleton n p
      return (.nu name s p, ls)

structure LiteralBinding where
  symbol : Kore.Modules.NamedSymbol
  literal : Literal
  deriving DecidableEq, Repr

structure HookBinding where
  symbol : Kore.Modules.NamedSymbol
  hook : Hook
  deriving DecidableEq, Repr

structure LoweredModule where
  source : Aliases.SourceModule
  literals : List LiteralBinding
  hooks : List HookBinding
  /-- Associates an original alias body with this module's literal namespace. -/
  aliases : List (Aliases.Declaration × Nat)

def lowerDeclaration (literalPrefix : String) (mi fuel : Nat) (skeleton : Bool) :
    Kore.Modules.Declaration RawPattern Aliases.Declaration →
      Option (Kore.Modules.Declaration RawPattern Aliases.Declaration × List Literal)
  | .sort n => some (.sort n, [])
  | .hookedSort _ _ => none
  | .importModule n => some (.importModule n, [])
  | .symbol d => some (.symbol d, [])
  | .hookedSymbol d name => do
      let h ← Hook.parse name
      if h.valid d then some (.symbol d, []) else none
  | .alias d => do
      let (body, ls) ← lowerPattern literalPrefix mi skeleton fuel d.body
      return (.alias {d with body := body}, ls)
  | .ruleAxiom p => do
      let (p, ls) ← lowerPattern literalPrefix mi skeleton fuel p
      return (.ruleAxiom p, ls)
  | .claim p => do
      let (p, ls) ← lowerPattern literalPrefix mi skeleton fuel p
      return (.claim p, ls)

/-- Original declarations and locations remain first, in their exact order;
only new literal declarations are appended, preserving every original origin. -/
def lowerModule (literalPrefix : String) (mi fuel : Nat) (skeleton : Bool)
    (m : Aliases.SourceModule) : Option LoweredModule := do
  let ds ← m.declarations.mapM fun d => do
    let (d', ls) ← lowerDeclaration literalPrefix mi fuel skeleton d.declaration
    return ((⟨d.location, d'⟩ : Kore.Modules.LocatedDeclaration RawPattern Aliases.Declaration), ls)
  let literals := (ds.flatMap Prod.snd).eraseDups
  let bindings := literals.zipIdx |>.map fun (l, i) =>
    LiteralBinding.mk ⟨⟨m.name, m.declarations.length + i⟩, literalDeclaration literalPrefix mi l⟩ l
  let extra := if skeleton then [] else bindings.map fun b =>
    (⟨m.location, .symbol b.symbol.declaration⟩ : Kore.Modules.LocatedDeclaration RawPattern Aliases.Declaration)
  let hooks ← (m.declarations.zipIdx).filterMapM fun (d, i) =>
    match d.declaration with
    | .hookedSymbol s name => do return some ⟨⟨⟨m.name, i⟩, s⟩, ← Hook.parse name⟩
    | _ => pure none
  let aliases := m.declarations.filterMap fun d =>
    match d.declaration with
    | .alias a => some (a, mi)
    | _ => none
  return ⟨{m with declarations := ds.map Prod.fst ++ extra}, bindings, hooks, aliases⟩

structure CheckedDefinition where
  source : Aliases.SourceDefinition
  literalPrefix : String
  fuel : Nat
  skeletonSource : Aliases.SourceDefinition
  skeleton : Aliases.Checking.CheckedDefinition
  lowered : List LoweredModule
  nativeSource : Aliases.SourceDefinition
  native : Aliases.Checking.CheckedDefinition
  prefix_fresh : literalPrefix = freshPrefix source
  lowered_checked : source.modules.zipIdx.mapM (fun (m, i) =>
    lowerModule literalPrefix i fuel false m) = some lowered
  native_source : nativeSource = ⟨lowered.map LoweredModule.source⟩
  skeleton_source : (do
    let ms ← source.modules.zipIdx.mapM (fun (m, i) => lowerModule literalPrefix i fuel true m)
    pure ({modules := ms.map LoweredModule.source} : Aliases.SourceDefinition)) = some skeletonSource
  skeleton_checked : Aliases.Checking.checkDefinition fuel skeletonSource = some skeleton
  native_checked : Aliases.Checking.checkDefinition fuel nativeSource = some native

/-- Check original visibility first, so generated declarations cannot accidentally
turn an undeclared source application into an accepted one. Both checks use the
existing complete module/import/alias checker. -/
def checkDefinition (fuel : Nat) (d : Aliases.SourceDefinition) : Option CheckedDefinition := do
  let literalPrefix := freshPrefix d
  match skeletonLoweredChecked : d.modules.zipIdx.mapM (fun (m, i) => lowerModule literalPrefix i fuel true m) with
  | none => none
  | some ms => do
    let skeletonSource : Aliases.SourceDefinition := ⟨ms.map LoweredModule.source⟩
    match skeletonChecked : Aliases.Checking.checkDefinition fuel skeletonSource with
    | none => none
    | some skeleton => do
      match loweredChecked : d.modules.zipIdx.mapM (fun (m, i) => lowerModule literalPrefix i fuel false m) with
      | none => none
      | some ms => do
        let nativeSource : Aliases.SourceDefinition := ⟨ms.map LoweredModule.source⟩
        match nativeChecked : Aliases.Checking.checkDefinition fuel nativeSource with
        | none => none
        | some native =>
          return ⟨d, literalPrefix, fuel, skeletonSource, skeleton, ms, nativeSource, native,
            rfl, loweredChecked, rfl,
            by simp only [skeletonLoweredChecked, bind, Option.bind, pure, Pure.pure, skeletonSource],
            skeletonChecked, nativeChecked⟩

theorem checkDefinition_input {fuel : Nat} {source : Aliases.SourceDefinition}
    {checked : CheckedDefinition} (accepted : checkDefinition fuel source = some checked) :
    checked.source = source ∧ checked.fuel = fuel := by
  unfold checkDefinition at accepted
  dsimp only at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · split at accepted
      · contradiction
      · split at accepted
        · contradiction
        · cases Option.some.inj accepted
          exact ⟨rfl, rfl⟩

def checkText (fuel : Nat) (text : String) : Option CheckedDefinition := do
  checkDefinition fuel (← Syntax.parse text)
end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
