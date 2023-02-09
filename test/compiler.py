#!/usr/bin/env python3
import argparse
import operator
import z3
import antlr4
from thorium import *
from typing import List
from thorium.z3types import Z3Types
from thorium.reactivetypes import *
from thorium.decls import *
from thorium.reactor_definer import ReactorDefiner


def lmap(f, iterable):
    return list(map(f, iterable))


# class Z3Types:
#     def __init__(self):
#         unit = z3.Datatype('unit')
#         unit.declare('unit')
#         unit = unit.create()
#         self.types = {'int': z3.IntSort(),
#                       'real': z3.RealSort(),
#                       'bool': z3.BoolSort(),
#                       'unit': unit}
#         self.datatypes = []
#         self.addDatatype(Stream('int'))
#         self.addDatatype(Stream('real'))
#         self.addDatatype(Stream('bool'))
#         self.addDatatype(Stream('unit'))
#
#     def addDatatype(self, datatype):
#         self.datatypes.append(datatype)
#         self.types[str(datatype)] = z3.Datatype(str(datatype))
#         if not isinstance(datatype, Stream):
#             self.addDatatype(Stream(datatype.name))
#
#     def __call__(self, type_):
#         if isinstance(type_, Cell):
#             return self.types[str(type_.type)]
#         return self.types[str(type_)]
#
#     def finalizeDatatypes(self):
#         for datatype in self.datatypes:
#             datatype.declareZ3Constructor(self)
#         datatype_names = [str(dt) for dt in self.datatypes]
#         args = [self(name) for name in datatype_names]
#         datatypes = z3.CreateDatatypes(*args)
#         self.types.update(
#             {name: datatype for name, datatype in zip(datatype_names, datatypes)})


class ParseDeclarations(ThoriumVisitor):
    def visitProg(self, ctx: ThoriumParser.ProgContext):
        return lmap(self.visit, ctx.decl())

    def visitDecl(self, ctx: ThoriumParser.DeclContext):
        return self.visit(ctx.children[0])  # there can be only one child

    def visitFunction(self, ctx: ThoriumParser.FunctionContext):
        return Function(ctx)

    def visitReactor(self, ctx: ThoriumParser.ReactorContext):
        return ReactorType(ctx,
                           ctx.ID().getText(),
                           self.visitOrDefault(ctx.reactorParams(), []),
                           self.visitOrDefault(ctx.reactorMembers(0), []),
                           self.visitOrDefault(ctx.reactorMembers(1), []),
                           self.visitOrDefault(ctx.reactorProperties(), []))

    def visitStruct(self, ctx: ThoriumParser.StructContext):
        return StructType(ctx,
                          ctx.ID().getText(),
                          self.visitOrDefault(ctx.structMembers(), []))

    def visitOrDefault(self, node, default):
        if node:
            return self.visit(node)
        return default

    def visitReactiveType(self, ctx: ThoriumParser.ReactiveTypeContext):
        if ctx.CELL():
            return Cell(self.visit(ctx.type_()))
        return Stream(self.visit(ctx.type_()))

    def visitType(self, ctx: ThoriumParser.TypeContext):
        return ctx.ID().getText()

    def visitReactorParams(self, ctx: ThoriumParser.ReactorParamsContext):
        return lmap(self.visit, ctx.reactorParam())

    def visitReactorParam(self, ctx: ThoriumParser.ReactorParamContext):
        return TypedIdentifier(ctx.ID().getText(), self.visit(ctx.reactiveType()))

    def visitStructMembers(self, ctx: ThoriumParser.StructMembersContext):
        return lmap(self.visit, ctx.structMember())

    def visitStructMember(self, ctx: ThoriumParser.StructMemberContext):
        return TypedIdentifier(ctx.ID().getText(), self.visit(ctx.type_()))

    def visitReactorMembers(self, ctx: ThoriumParser.ReactorMembersContext):
        return lmap(self.visit, ctx.reactorMember())

    def visitReactorMember(self, ctx: ThoriumParser.ReactorMemberContext):
        return TypedIdentifier(ctx.ID().getText(), self.visit(ctx.reactiveType()))

    def visitReactorProperties(self, ctx: ThoriumParser.ReactorPropertiesContext):
        return lmap(self.visit, ctx.reactorProperty())

    def visitReactorProperty(self, ctx: ThoriumParser.ReactorPropertyContext):
        return TypedIdentifier(ctx.ID().getText(), Cell('bool'))


def hasStreamType(types):
    for type_ in types:
        if isinstance(type_, Stream):
            return True
    return False


class SubExprTypeCheck(ThoriumVisitor):
    def __init__(self, decls):
        self.decls = decls
        self.reactor = None

    def expr_name(self, ctx):
        return self.reactor.expr_name(ctx)

    def set_expr_name(self, ctx, name):
        self.reactor.set_expr_name(ctx, name)

    def visitSubExpr(self, ctx, sub=None):
        if not sub:  # todo: move to param list
            sub = ctx.expr()
        self.set_expr_name(sub, f'{self.expr_name(ctx)}-1')
        type_ = self.visit(sub)
        self.reactor.addSubExpr(sub, type_)
        return type_

    def visitSubExprs(self, ctx, subs=None):
        types = []
        if not subs:
            subs = ctx.expr()
        for i, sub in enumerate(subs):
            self.set_expr_name(sub, f'{self.expr_name(ctx)}-{i + 1}')
            type_ = self.visit(sub)
            types.append(type_)
            self.reactor.addSubExpr(sub, type_)
        return types

    def visitFunction(self, ctx: ThoriumParser.FunctionContext):
        pass  # todo: implement type checking

    def visitReactor(self, ctx: ThoriumParser.ReactorContext):
        self.reactor = self.decls[ctx.ID().getText()]
        for m in ctx.reactorMembers():
            self.visit(m)
        if ctx.reactorProperties():
            self.visit(ctx.reactorProperties())

    def visitReactorMember(self, ctx: ThoriumParser.ReactorMemberContext):
        self.set_expr_name(ctx.expr(), ctx.ID().getText())
        # todo: typecheck
        self.visit(ctx.expr())

    def visitReactorProperty(self, ctx: ThoriumParser.ReactorPropertyContext):
        self.set_expr_name(ctx.property_(), ctx.ID().getText())
        self.visit(ctx.property_())

    def visitProperty(self, ctx: ThoriumParser.PropertyContext):
        if ctx.ltlProperty():
            self.set_expr_name(ctx.ltlProperty(), self.expr_name(ctx))
            return self.visit(ctx.ltlProperty())

    def visitLtlNegation(self, ctx: ThoriumParser.LtlNegationContext):
        self.visitSubExpr(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlParen(self, ctx: ThoriumParser.LtlParenContext):
        self.set_expr_name(ctx.ltlProperty(), self.expr_name(ctx))
        return self.visit(ctx.ltlProperty())

    def visitLtlNext(self, ctx: ThoriumParser.LtlNextContext):
        self.visitSubExpr(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlGlobally(self, ctx: ThoriumParser.LtlGloballyContext):
        self.visitSubExpr(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlEventually(self, ctx: ThoriumParser.LtlEventuallyContext):
        self.visitSubExpr(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlUntil(self, ctx: ThoriumParser.LtlUntilContext):
        self.visitSubExprs(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlSince(self, ctx: ThoriumParser.LtlSinceContext):
        self.visitSubExprs(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlAnd(self, ctx: ThoriumParser.LtlAndContext):
        self.visitSubExprs(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlOr(self, ctx: ThoriumParser.LtlAndContext):
        self.visitSubExprs(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlImplication(self, ctx: ThoriumParser.LtlImplicationContext):
        self.visitSubExprs(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlExpr(self, ctx: ThoriumParser.LtlExprContext):
        self.set_expr_name(ctx.expr(), self.expr_name(ctx))
        return self.visit(ctx.expr())

    def visitApply(self, ctx: ThoriumParser.ApplyContext):
        types = self.visitSubExprs(ctx)
        if ctx.ID().getText() == 'unit':
            result_type = 'unit'
        else:
            f = self.decls[ctx.ID().getText()]
            if isinstance(f, Function):
                result_type = f.result_type
            else:  # struct, for now
                result_type = f.name
        if hasStreamType(types):
            return Stream(result_type)
        return result_type

    def visitNegative(self, ctx: ThoriumParser.NegativeContext):
        self.set_expr_name(ctx.expr(), f'{self.expr_name(ctx)}-1')
        type_ = self.visit(ctx.expr())
        self.reactor.addSubExpr(ctx.expr(), type_)
        return type_

    def visitMemberAccess(self, ctx: ThoriumParser.MemberAccessContext):
        self.set_expr_name(ctx.expr(), f'{self.expr_name(ctx)}-1')
        type_ = self.visit(ctx.expr())
        self.reactor.addSubExpr(ctx.expr(), type_)

        composite_type = self.decls[base_type(type_)]
        member_type = composite_type.getPublicMemberType(ctx.ID().getText())
        if isinstance(type_, Stream):
            return Stream(member_type)
        return member_type

    def visitId(self, ctx: ThoriumParser.IdContext):
        return self.reactor.getType(ctx.ID().getText())

    def visitChanges(self, ctx: ThoriumParser.ChangesContext):
        self.set_expr_name(ctx.expr(), f'{self.expr_name(ctx)}-1')
        type_ = self.visit(ctx.expr())
        self.reactor.addSubExpr(ctx.expr(), type_)
        return Stream(type_)

    def visitNumber(self, ctx: ThoriumParser.NumberContext):
        return 'int'

    def visitUnit(self, ctx: ThoriumParser.UnitContext):
        return 'unit'

    def visitBool(self, ctx: ThoriumParser.BoolContext):
        return 'bool'

    def visitParen(self, ctx: ThoriumParser.ParenContext):
        self.set_expr_name(ctx.expr(), self.expr_name(ctx))
        return self.visit(ctx.expr())

    def visitMult(self, ctx: ThoriumParser.MultContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types):
            return Stream('int')
        return Cell('int')

    def visitAdd(self, ctx: ThoriumParser.AddContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types):
            return Stream('int')
        return Cell('int')

    def visitCompare(self, ctx: ThoriumParser.CompareContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types):
            return Stream('bool')
        return Cell('bool')

    def visitEquals(self, ctx: ThoriumParser.EqualsContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types):
            return Stream('bool')
        return Cell('bool')

    def visitNot(self, ctx: ThoriumParser.NotContext):
        type_ = self.visitSubExpr(ctx)
        if isinstance(type_, Stream):
            return Stream('bool')
        return Cell('bool')

    def visitAnd(self, ctx: ThoriumParser.AndContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types):
            return Stream('bool')
        return Cell('bool')

    def visitOr(self, ctx: ThoriumParser.AndContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types):
            return Stream('bool')
        return Cell('bool')

    def visitImplication(self, ctx: ThoriumParser.ImplicationContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types):
            return Stream('bool')
        return Cell('bool')

    def visitFilter(self, ctx: ThoriumParser.FilterContext):
        type_, _ = self.visitSubExprs(ctx)
        # TODO: typeCheck
        return Stream(type_)

    def visitSnapshot(self, ctx: ThoriumParser.SnapshotContext):
        type_, _ = self.visitSubExprs(ctx)
        # TODO: typeCheck
        return Stream(type_)

    def visitMerge(self, ctx: ThoriumParser.MergeContext):
        type_, _ = self.visitSubExprs(ctx)
        # TODO: typeCheck (both should be the same kind of stream)
        return type_

    def visitHold(self, ctx: ThoriumParser.HoldContext):
        type_, _ = self.visitSubExprs(ctx)
        # TODO: typeCheck (both should hold the same kind of value)
        return Cell(type_)


def named_lookup(named_items: List):
    return {t.name: t for t in named_items}


def parse_thorium_file(filename):
    input_stream = antlr4.FileStream(filename)
    lexer = ThoriumLexer(input_stream)
    stream = antlr4.CommonTokenStream(lexer)
    parser = ThoriumParser(stream)
    tree = parser.prog()

    declarations = ParseDeclarations().visitProg(tree)
    SubExprTypeCheck(named_lookup(declarations)).visitProg(tree)
    z3_types = Z3Types()
    composite_types = []
    functions = []
    for declaration in declarations:
        if isinstance(declaration, Function):
            functions.append(declaration)
        else:
            z3_types.addDatatype(declaration)
            composite_types.append(declaration)
    z3_types.finalizeDatatypes()
    for f in functions:
        f.setTypeContext(z3_types)

    return named_lookup(composite_types), named_lookup(functions), z3_types


def main(_argv):
    argparser = argparse.ArgumentParser(prog='thorium-verifier',
                                        description='Verifies reactor properties.')

    argparser.add_argument('filename')
    argparser.add_argument('-r', '--reactor', dest='reactor', required=True)
    argparser.add_argument('-p', '--property', dest='property', required=True)
    argparser.add_argument('-n', '--num-states', dest='N', type=int, required=True)
    argparser.add_argument('-f', '--full-model', dest='full_model', action='store_true', default=False)

    args = argparser.parse_args()

    composite_types, functions, z3_types = parse_thorium_file(args.filename)

    reactor_definer = ReactorDefiner(composite_types, functions, z3_types)
    solver = z3.Solver()
    reactor = reactor_definer(f'{args.reactor}-main', args.reactor, 0, args.N, solver)
    reactor_type = z3_types(args.reactor)
    thorium_reactor = composite_types[args.reactor]

    # print(repr(thorium_reactor))

    property_ = reactor_type.__getattribute__(args.property)

    solver.add(z3.Not(property_(reactor(0))))

    verification_result = solver.check()

    # print(solver.statistics())
    # print(solver.statistics().keys())

    print(f"Time      : {solver.statistics().get_key_value('time')} seconds")
    print(f"Max memory: {solver.statistics().get_key_value('max memory')}")

    if verification_result == z3.sat:
        z3_trace = solver.model()[reactor]
        f = {a.as_long(): b for a, b in z3_trace.as_list()[:-1]}
        trace = []
        if args.full_model:
            namegetter = thorium_reactor.getMemberNames
            getter = thorium_reactor.getMemberValues
        else:
            namegetter = thorium_reactor.getDeclaredMemberNames
            getter = thorium_reactor.getDeclaredMemberValues
        for k in range(args.N + 1):
            if k in f:
                trace.append(getter(f[k]))
            else:
                trace.append(getter(z3_trace.else_value()))

        trace = [namegetter()] + trace
        column_widths = [max([len(name) for name in column]) for column in trace]
        format_string = ' & '.join(('%%%ds' % width) for width in column_widths) + r' \\'
        print(r'\begin{centering}')
        print(r'\begin{tabular}{%s}' % ('|c' * len(column_widths) + '|'))
        print(r'\hline')
        print(format_string % tuple(['k'] + list(range(len(column_widths) - 1))))
        print(r'\hline')
        for row in [[t[i] for t in trace] for i in range(len(trace[0]))]:
            print(format_string % tuple(row))
        print(r'\hline')
        print(r'\end{tabular}\\')
        print(r'\end{centering}')

    if verification_result == z3.unsat:
        print(f'Property "{args.property}" for reactor "{args.reactor}" holds for all runs of {args.N} steps.')


if __name__ == '__main__':
    main(sys.argv)
