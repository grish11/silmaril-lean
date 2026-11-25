#!/usr/bin/env python3
"""Emit Silmaril Python Source.Module constructors from an external CPython AST."""

import argparse
import ast
import json
import struct
import sys
import tokenize
from pathlib import Path


class UnsupportedSyntax(ValueError):
    def __init__(self, node: ast.AST):
        super().__init__(f"{node.lineno}:{node.col_offset + 1}: unsupported {type(node).__name__}")


def quote(name):
    return json.dumps(name, ensure_ascii=False)


def lean_list(items):
    return "[" + ", ".join(items) + "]"


def constructor(name, *fields):
    if not fields:
        return "." + name
    return "(." + name + " " + " ".join(fields) + ")"


def option(value, render):
    return "none" if value is None else f"(some {render(value)})"


def pair(a, b):
    return f"({a}, {b})"


BINARY = {
    ast.Add: ".add", ast.Sub: ".sub", ast.Mult: ".mul", ast.Div: ".trueDiv",
    ast.FloorDiv: ".floorDiv", ast.Mod: ".modulo", ast.Pow: ".pow", ast.MatMult: ".matrixMul",
    ast.BitAnd: ".bitAnd", ast.BitOr: ".bitOr", ast.BitXor: ".bitXor",
    ast.LShift: ".shiftLeft", ast.RShift: ".shiftRight",
}
UNARY = {ast.UAdd: ".positive", ast.USub: ".negative", ast.Invert: ".invert", ast.Not: ".not_"}
BOOLEAN = {ast.And: ".and_", ast.Or: ".or_"}
COMPARISONS = {
    ast.Eq: ".eq", ast.NotEq: ".ne", ast.Lt: ".lt", ast.LtE: ".le", ast.Gt: ".gt", ast.GtE: ".ge",
    ast.Is: ".is_", ast.IsNot: ".isNot", ast.In: ".in_", ast.NotIn: ".notIn",
}
UNSUPPORTED_EXPRESSIONS = {
    ast.ListComp: ".listComprehension", ast.SetComp: ".setComprehension",
    ast.DictComp: ".dictComprehension", ast.GeneratorExp: ".generatorExpression",
}


def literal(node):
    value = node.value
    if value is None:
        return ".none_"
    if value is Ellipsis:
        return ".ellipsis"
    if isinstance(value, bool):
        return constructor("boolean", str(value).lower())
    if isinstance(value, int):
        return constructor("integer", hex(value))
    if isinstance(value, float):
        return constructor("floatBits", str(int.from_bytes(struct.pack(">d", value), "big")))
    if isinstance(value, str):
        return constructor("text", lean_list(str(ord(character)) for character in value))
    if isinstance(value, bytes):
        return constructor("unsupported", ".bytesLiteral")
    raise UnsupportedSyntax(node)


def parameters(arguments):
    positional = [(arg, ".positionalOnly") for arg in arguments.posonlyargs]
    positional += [(arg, ".positionalOrKeyword") for arg in arguments.args]
    defaults = [None] * (len(positional) - len(arguments.defaults)) + arguments.defaults
    fields = [(arg, kind, default) for (arg, kind), default in zip(positional, defaults)]
    if arguments.vararg is not None:
        fields.append((arguments.vararg, ".varPositional", None))
    fields += [(arg, ".keywordOnly", default)
               for arg, default in zip(arguments.kwonlyargs, arguments.kw_defaults)]
    if arguments.kwarg is not None:
        fields.append((arguments.kwarg, ".varKeyword", None))
    return lean_list(
        f"{{ name := {quote(arg.arg)}, kind := {kind}, "
        f"defaultValue := {option(default, expression)}, annotation := {option(arg.annotation, expression)} }}"
        for arg, kind, default in fields
    )


def call_argument(argument):
    if isinstance(argument, ast.Starred):
        return pair(".unpackIterable", expression(argument.value))
    return pair(".positional", expression(argument))


def call_keyword(keyword):
    kind = ".unpackMapping" if keyword.arg is None else constructor("keyword", quote(keyword.arg))
    return pair(kind, expression(keyword.value))


def subscript(node, *, target=False):
    if isinstance(node.slice, ast.Slice):
        if target:
            raise UnsupportedSyntax(node.slice)
        bounds = [option(bound, expression) for bound in (node.slice.lower, node.slice.upper, node.slice.step)]
        return constructor("slice", expression(node.value), *bounds)
    return constructor("subscript", expression(node.value), expression(node.slice))


def expression(node):
    match node:
        case ast.Constant():
            return literal(node)
        case ast.Name(id=name):
            return constructor("name", quote(name))
        case ast.List(elts=elements) | ast.Tuple(elts=elements):
            kind = "list_" if isinstance(node, ast.List) else "tuple"
            return constructor(kind, lean_list(map(expression, elements)))
        case ast.Dict(keys=keys, values=values):
            entries = (pair(option(key, expression), expression(value)) for key, value in zip(keys, values))
            return constructor("dictionary", lean_list(entries))
        case ast.UnaryOp(op=op, operand=operand):
            return constructor("unary", UNARY[type(op)], expression(operand))
        case ast.BinOp(left=left, op=op, right=right):
            return constructor("binary", BINARY[type(op)], expression(left), expression(right))
        case ast.BoolOp(op=op, values=values):
            return constructor("booleanOp", BOOLEAN[type(op)], lean_list(map(expression, values)))
        case ast.IfExp(test=test, body=body, orelse=otherwise):
            return constructor("conditional", expression(test), expression(body), expression(otherwise))
        case ast.Compare(left=left, ops=ops, comparators=comparands):
            rest = (pair(COMPARISONS[type(op)], expression(value)) for op, value in zip(ops, comparands))
            return constructor("comparison", expression(left), lean_list(rest))
        case ast.Call(func=callee, args=args, keywords=keywords):
            rendered = [*map(call_argument, args), *map(call_keyword, keywords)]
            return constructor("callWith", expression(callee), lean_list(rendered))
        case ast.Starred(value=value, ctx=ast.Load()):
            return constructor("starred", expression(value))
        case ast.Attribute(value=value, attr=name):
            return constructor("attribute", expression(value), quote(name))
        case ast.Subscript():
            return subscript(node)
        case ast.Yield(value=value):
            return constructor("yield_", option(value, expression))
        case ast.Lambda(args=args, body=body):
            return constructor("lambda", parameters(args), expression(body))
    if type(node) in UNSUPPORTED_EXPRESSIONS:
        return constructor("unsupported", UNSUPPORTED_EXPRESSIONS[type(node)])
    raise UnsupportedSyntax(node)


def binding_target(node):
    match node:
        case ast.Name(id=name):
            return constructor("name", quote(name))
        case ast.Attribute(value=value, attr=name):
            return constructor("attribute", expression(value), quote(name))
        case ast.Subscript():
            return subscript(node, target=True)
        case ast.Tuple(elts=elements) | ast.List(elts=elements):
            kind = "tuple" if isinstance(node, ast.Tuple) else "list_"
            return constructor(kind, lean_list(map(binding_target, elements)))
    raise UnsupportedSyntax(node)


def suite(nodes):
    return lean_list(map(statement, nodes))


def handler(node):
    return ("{ condition := " + option(node.type, expression)
            + ", target := " + option(node.name, quote) + ", body := " + suite(node.body) + " }")


def import_name(alias):
    return f"{{ member := {quote(alias.name)}, «alias» := {option(alias.asname, quote)} }}"


def statement(node):
    match node:
        case ast.Assign(targets=targets, value=value):
            return constructor("assignTargets", lean_list(map(binding_target, targets)), expression(value))
        case ast.Delete(targets=targets):
            return constructor("deleteTargets", lean_list(map(binding_target, targets)))
        case ast.Expr(value=value):
            return constructor("expression", expression(value))
        case ast.Return(value=value):
            return constructor("return_", option(value, expression))
        case ast.Raise(exc=exception, cause=cause):
            return constructor("raise_", option(exception, expression), option(cause, expression))
        case ast.Assert(test=test, msg=message):
            return constructor("assert_", expression(test), option(message, expression))
        case ast.Pass():
            return ".pass"
        case ast.Break():
            return ".break_"
        case ast.Continue():
            return ".continue_"
        case ast.Global(names=names) | ast.Nonlocal(names=names):
            kind = "globalDecl" if isinstance(node, ast.Global) else "nonlocalDecl"
            return constructor(kind, lean_list(map(quote, names)))
        case ast.If(test=test, body=body, orelse=otherwise) | ast.While(test=test, body=body, orelse=otherwise):
            kind = "if_" if isinstance(node, ast.If) else "while_"
            return constructor(kind, expression(test), suite(body), suite(otherwise))
        case ast.For(target=target, iter=iterator, body=body, orelse=otherwise):
            return constructor("for_", binding_target(target), expression(iterator), suite(body), suite(otherwise))
        case ast.Try(body=body, handlers=handlers, orelse=otherwise, finalbody=cleanup):
            return constructor("try_", suite(body), lean_list(map(handler, handlers)), suite(otherwise), suite(cleanup))
        case ast.ImportFrom(module=module, level=level, names=names):
            path = [] if module is None else module.split(".")
            return constructor("importFrom", lean_list(map(quote, path)), str(level), lean_list(map(import_name, names)))
        case ast.FunctionDef(name=name, args=args, body=body, decorator_list=decorators, returns=returns):
            return constructor("functionDef", quote(name), parameters(args), suite(body),
                               lean_list(map(expression, decorators)), option(returns, expression))
        case ast.ClassDef(name=name, bases=bases, keywords=keywords, body=body, decorator_list=decorators):
            keywords = (pair(option(keyword.arg, quote), expression(keyword.value)) for keyword in keywords)
            return constructor("classDef", quote(name), lean_list(map(expression, bases)), suite(body),
                               lean_list(map(expression, decorators)), lean_list(keywords))
    raise UnsupportedSyntax(node)


def emit(module):
    body = ",\n    ".join(map(statement, module.body))
    return ("module\n\n"
            "public import Silmaril.Languages.Python.Source.Syntax.Defs\n\n"
            "open Silmaril.Languages.Python.Source\n\n"
            "public def pythonSource : Module :=\n"
            "  { body := [\n"
            f"    {body}] }}\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--output", type=Path, help="Write the generated Lean module to this path")
    args = parser.parse_args()
    try:
        with tokenize.open(args.source) as source:
            module = ast.parse(source.read(), filename=str(args.source), feature_version=(3, 7))
        rendered = emit(module)
        if args.output is None:
            sys.stdout.write(rendered)
        else:
            args.output.write_text(rendered, encoding="utf-8")
    except (OSError, SyntaxError, UnicodeError, UnsupportedSyntax) as error:
        parser.exit(1, f"{args.source}: {error}\n")


if __name__ == "__main__":
    main()
