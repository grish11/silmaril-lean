module

public import Silmaril.Logic.Temporal.TLA.Surface.Defs
import Std.Data.HashMap

public section

namespace Silmaril.Logic.Temporal.TLA.Surface.Parser

inductive Fixity where
  | prefix | infix | postfix | product
  deriving BEq, Inhabited

structure Operator where
  canonical : String
  low : Nat
  high : Nat
  leftAssociative : Bool
  fixity : Fixity
  deriving Inhabited

/-- Precedence intervals and aliases from SANY's pinned `Operators.java`.
Aliases share operator identity for precedence and associativity. -/
def operatorGroups : List (Operator × List String) := [
  (⟨"[", 160, 160, true, .postfix⟩, []),
  (⟨".", 170, 170, true, .infix⟩, []),
  (⟨"'", 150, 150, false, .postfix⟩, []),
  (⟨"^", 140, 140, false, .infix⟩, []),
  (⟨"/", 130, 130, false, .infix⟩, []),
  (⟨"*", 130, 130, true, .infix⟩, []),
  (⟨"-", 110, 110, true, .infix⟩, []),
  (⟨"-.", 120, 120, false, .prefix⟩, []),
  (⟨"+", 100, 100, true, .infix⟩, []),
  (⟨"=", 50, 50, false, .infix⟩, []),
  (⟨"\\lnot", 40, 40, true, .prefix⟩, ["~", "\\neg", "¬"]),
  (⟨"\\land", 30, 30, true, .infix⟩, ["/\\", "∧"]),
  (⟨"\\lor", 30, 30, true, .infix⟩, ["\\/", "∨"]),
  (⟨"~>", 20, 20, false, .infix⟩, ["↝"]),
  (⟨"=>", 10, 10, false, .infix⟩, ["⇒"]),
  (⟨"[]", 40, 150, false, .prefix⟩, ["□"]),
  (⟨"<>", 40, 150, false, .prefix⟩, ["◇"]),
  (⟨"ENABLED", 40, 150, false, .prefix⟩, []),
  (⟨"UNCHANGED", 40, 150, false, .prefix⟩, []),
  (⟨"SUBSET", 80, 80, false, .prefix⟩, []),
  (⟨"UNION", 80, 80, false, .prefix⟩, []),
  (⟨"DOMAIN", 90, 90, false, .prefix⟩, []),
  (⟨"^+", 150, 150, false, .postfix⟩, ["⁺"]),
  (⟨"^*", 150, 150, false, .postfix⟩, []),
  (⟨"^#", 150, 150, false, .postfix⟩, []),
  (⟨"\\cdot", 50, 140, true, .infix⟩, ["⋅"]),
  (⟨"\\equiv", 20, 20, false, .infix⟩, ["<=>", "≡", "⇔"]),
  (⟨"-+->", 20, 20, false, .infix⟩, ["⇸"]),
  (⟨"/=", 50, 50, false, .infix⟩, ["#", "≠"]),
  (⟨"\\subseteq", 50, 50, false, .infix⟩, ["⊆"]),
  (⟨"\\in", 50, 50, false, .infix⟩, ["∈"]),
  (⟨"\\notin", 50, 50, false, .infix⟩, ["∉"]),
  (⟨"<", 50, 50, false, .infix⟩, []),
  (⟨"\\leq", 50, 50, false, .infix⟩, ["<=", "=<", "≤"]),
  (⟨">", 50, 50, false, .infix⟩, []),
  (⟨"\\geq", 50, 50, false, .infix⟩, [">=", "≥"]),
  (⟨"\\times", 100, 130, true, .product⟩, ["\\X", "×"]),
  (⟨"\\", 80, 80, false, .infix⟩, []),
  (⟨"\\intersect", 80, 80, true, .infix⟩, ["\\cap", "∩"]),
  (⟨"\\union", 80, 80, true, .infix⟩, ["\\cup", "∪"]),
  (⟨"...", 90, 90, false, .infix⟩, ["…"]),
  (⟨"..", 90, 90, false, .infix⟩, ["‥"]),
  (⟨"|", 100, 110, true, .infix⟩, []),
  (⟨"||", 100, 110, true, .infix⟩, ["‖"]),
  (⟨"&&", 130, 130, true, .infix⟩, []),
  (⟨"&", 130, 130, true, .infix⟩, []),
  (⟨"$$", 90, 130, true, .infix⟩, []),
  (⟨"$", 90, 130, true, .infix⟩, []),
  (⟨"??", 90, 130, true, .infix⟩, ["⁇"]),
  (⟨"%%", 100, 110, true, .infix⟩, []),
  (⟨"%", 100, 110, false, .infix⟩, []),
  (⟨"##", 90, 130, true, .infix⟩, []),
  (⟨"++", 100, 100, true, .infix⟩, []),
  (⟨"--", 110, 110, true, .infix⟩, []),
  (⟨"**", 130, 130, true, .infix⟩, []),
  (⟨"//", 130, 130, false, .infix⟩, []),
  (⟨"^^", 140, 140, false, .infix⟩, []),
  (⟨"@@", 60, 60, true, .infix⟩, []),
  (⟨"!!", 90, 130, false, .infix⟩, ["‼"]),
  (⟨"|-", 50, 50, false, .infix⟩, ["⊢"]),
  (⟨"|=", 50, 50, false, .infix⟩, ["⊨"]),
  (⟨"-|", 50, 50, false, .infix⟩, ["⊣"]),
  (⟨"=|", 50, 50, false, .infix⟩, ["⫤"]),
  (⟨"<:", 70, 70, false, .infix⟩, []),
  (⟨":>", 70, 70, false, .infix⟩, []),
  (⟨":=", 50, 50, false, .infix⟩, ["≔"]),
  (⟨"::=", 50, 50, false, .infix⟩, ["⩴"]),
  (⟨"\\oplus", 100, 100, true, .infix⟩, ["(+)", "⊕"]),
  (⟨"\\ominus", 110, 110, true, .infix⟩, ["(-)", "⊖"]),
  (⟨"\\odot", 130, 130, true, .infix⟩, ["(.)", "⊙"]),
  (⟨"\\oslash", 130, 130, false, .infix⟩, ["(/)", "⊘"]),
  (⟨"\\otimes", 130, 130, true, .infix⟩, ["(\\X)", "⊗"]),
  (⟨"\\uplus", 90, 130, true, .infix⟩, ["⊎"]),
  (⟨"\\sqcap", 90, 130, true, .infix⟩, ["⊓"]),
  (⟨"\\sqcup", 90, 130, true, .infix⟩, ["⊔"]),
  (⟨"\\div", 130, 130, false, .infix⟩, ["÷"]),
  (⟨"\\wr", 90, 140, false, .infix⟩, ["≀"]),
  (⟨"\\star", 130, 130, true, .infix⟩, ["⋆"]),
  (⟨"\\o", 130, 130, true, .infix⟩, ["\\circ", "∘"]),
  (⟨"\\bigcirc", 130, 130, true, .infix⟩, ["◯"]),
  (⟨"\\bullet", 130, 130, true, .infix⟩, ["●"]),
  (⟨"\\prec", 50, 50, false, .infix⟩, ["≺"]),
  (⟨"\\succ", 50, 50, false, .infix⟩, ["≻"]),
  (⟨"\\preceq", 50, 50, false, .infix⟩, ["⪯"]),
  (⟨"\\succeq", 50, 50, false, .infix⟩, ["⪰"]),
  (⟨"\\sim", 50, 50, false, .infix⟩, ["∼"]),
  (⟨"\\simeq", 50, 50, false, .infix⟩, ["≃"]),
  (⟨"\\ll", 50, 50, false, .infix⟩, ["≪"]),
  (⟨"\\gg", 50, 50, false, .infix⟩, ["≫"]),
  (⟨"\\asymp", 50, 50, false, .infix⟩, ["≍"]),
  (⟨"\\subset", 50, 50, false, .infix⟩, ["⊂"]),
  (⟨"\\supset", 50, 50, false, .infix⟩, ["⊃"]),
  (⟨"\\supseteq", 50, 50, false, .infix⟩, ["⊇"]),
  (⟨"\\approx", 50, 50, false, .infix⟩, ["≈"]),
  (⟨"\\cong", 50, 50, false, .infix⟩, ["≅"]),
  (⟨"\\sqsubset", 50, 50, false, .infix⟩, ["⊏"]),
  (⟨"\\sqsubseteq", 50, 50, false, .infix⟩, ["⊑"]),
  (⟨"\\sqsupset", 50, 50, false, .infix⟩, ["⊐"]),
  (⟨"\\sqsupseteq", 50, 50, false, .infix⟩, ["⊒"]),
  (⟨"\\doteq", 50, 50, false, .infix⟩, ["≐"]),
  (⟨"\\propto", 50, 50, false, .infix⟩, ["∝"])]


private def operatorTable : Std.HashMap String Operator :=
  operatorGroups.foldl (fun table (op, aliases) =>
    (op.canonical :: aliases).foldl (fun table spelling => table.insert spelling op) table)
    {}

def lookupOperator (spelling : String) : Option Operator := operatorTable[spelling]?

def Operator.prefixOp (op : Operator) (spelling : String) : PrefixOp :=
  match op.canonical with
  | "\\lnot" => .negation
  | "-." => .minus
  | "ENABLED" => .enabled
  | "UNCHANGED" => .unchanged
  | "[]" => .always
  | "<>" => .eventually
  | "SUBSET" => .subset
  | "UNION" => .union
  | "DOMAIN" => .domain
  | _ => .symbol spelling

def Operator.infixOp (op : Operator) (spelling : String) : InfixOp :=
  match op.canonical with
  | "\\cdot" => .compose
  | "~>" => .leadsTo
  | "-+->" => .guarantees
  | _ => .symbol spelling

def Operator.postfixOp (op : Operator) (spelling : String) : PostfixOp :=
  if op.canonical == "'" then .prime else .symbol spelling

end Silmaril.Logic.Temporal.TLA.Surface.Parser
