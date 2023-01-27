#!/usr/bin/env python3
import argparse
import operator
import z3
import antlr4
from thorium import *
from typing import List


def lmap(f, iterable):
    return list(map(f, iterable))


class Cell:
    def __init__(self, type_):
        if isinstance(type_, Stream) or isinstance(type_, Cell):
            self.type = type_.type
        else:
            self.type = type_

    def __str__(self):
        return f'cell-{self.type}'


class Stream:
    def __init__(self, type_):
        if isinstance(type_, Stream) or isinstance(type_, Cell):
            self.type = type_.type
        else:
            self.type = type_
        self.name = self

    def declareZ3Constructor(self, type_ctx):
        type_ctx(self).declare('event', ('value', type_ctx(self.type)))
        type_ctx(self).declare('nothing')

    def __str__(self):
        return f'stream-{self.type}'

    def __eq__(self, other):
        return isinstance(other, Stream) and (self.type == other.type)


def base_type(type_):
    if isinstance(type_, Cell):
        return type_.type
    if isinstance(type_, Stream):
        return type_.type
    return type_


class TypedIdentifier:
    def __init__(self, name, type_):
        self.name = name
        self.type = type_

    def __repr__(self):
        return f'{self.name} : {self.type}'


class Operators:
    unary = {'-': operator.neg,
             'not': operator.not_}
    binary = {'+': operator.add,
              '-': operator.sub,
              '*': operator.mul,
              '/': operator.truediv,
              '<': operator.lt,
              '<=': operator.le,
              '>': operator.gt,
              '>=': operator.ge,
              '==': operator.eq,
              '!=': operator.ne,
              '->': z3.Implies,
              'and': z3.And,
              'or': z3.Or,
              }


class Function(ThoriumVisitor):
    def __init__(self, ctx: ThoriumParser.FunctionContext):
        self.solver = None
        self.name = None
        self.params = None
        self.result_type = None
        self.properties = None
        self.f = None
        self.visit(ctx)

    def unaryOp(self, ctx):
        f = Operators.unary[ctx.op.text]
        arg = self.visit(ctx.expr())
        return f(arg)

    def binOp(self, ctx):
        f = Operators.binary[ctx.op.text]
        arg0 = self.visit(ctx.expr(0))
        arg1 = self.visit(ctx.expr(1))
        return f(arg0, arg1)

    def setSolver(self, solver):
        self.solver = solver

    def __call__(self, *args):
        self.symbols = {p.name: a for p, a in zip(self.params, args)}
        self.symbols['result'] = self.f(*args)
        self.visit(self.properties)
        return self.f(*args)

    def visitFunction(self, ctx: ThoriumParser.FunctionContext):
        self.name = ctx.ID().getText()
        self.params = self.visit(ctx.functionParams())
        self.result_type = self.visit(ctx.type_())
        self.properties = ctx.functionProperties()

    def setTypeContext(self, z3_types):
        args = [self.name] + [z3_types(param.type) for param in self.params] + [z3_types(self.result_type)]
        self.f = z3.Function(*args)

    def visitFunctionParams(self, ctx: ThoriumParser.FunctionParamsContext):
        return [self.visit(param) for param in ctx.functionParam()]

    def visitFunctionParam(self, ctx: ThoriumParser.FunctionParamContext):
        return TypedIdentifier(ctx.ID().getText(), self.visit(ctx.type_()))

    def visitType(self, ctx: ThoriumParser.TypeContext):
        return ctx.ID().getText()

    def visitFunctionProperty(self, ctx: ThoriumParser.FunctionPropertyContext):
        self.solver.add(self.visit(ctx.expr()))

    def visitMemberAccess(self, ctx: ThoriumParser.MemberAccessContext):
        print('*************************************** not implemented')
        pass

    def visitId(self, ctx: ThoriumParser.IdContext):
        return self.symbols[ctx.ID().getText()]

    def visitNumber(self, ctx: ThoriumParser.NumberContext):
        return int(ctx.NUMBER().getText())

    def visitParen(self, ctx: ThoriumParser.ParenContext):
        return self.visit(ctx.expr())

    def visitMult(self, ctx: ThoriumParser.MultContext):
        return self.binOp(ctx)

    def visitAdd(self, ctx: ThoriumParser.AddContext):
        return self.binOp(ctx)

    def visitCompare(self, ctx: ThoriumParser.CompareContext):
        return self.binOp(ctx)

    def visitEquals(self, ctx: ThoriumParser.EqualsContext):
        return self.binOp(ctx)

    def visitNot(self, ctx: ThoriumParser.NotContext):
        return self.unaryOp(ctx)

    def visitAnd(self, ctx: ThoriumParser.AndContext):
        return self.binOp(ctx)

    def visitOr(self, ctx: ThoriumParser.AndContext):
        return self.binOp(ctx)

    def visitImplication(self, ctx: ThoriumParser.ImplicationContext):
        return self.binOp(ctx)


class ReactorType:
    def __init__(self, ctx: ThoriumParser.ReactorContext,
                       name: str,
                       params: List[TypedIdentifier],
                       public_members: List[TypedIdentifier],
                       private_members: List[TypedIdentifier],
                       properties: List[TypedIdentifier]):
        self.ctx = ctx
        self.name = name
        self.params = params
        self.params_dict = {m.name: m.type for m in params}
        self.public_members = public_members
        self.public_members_dict = {m.name: m.type for m in public_members}
        self.private_members = private_members
        self.private_members_dict = {m.name: m.type for m in private_members}
        self.properties = properties
        self.properties_dict = {m.name: m.type for m in properties}
        self.all_members = {}
        self.all_members.update(self.params_dict)
        self.all_members.update(self.public_members_dict)
        self.all_members.update(self.private_members_dict)
        self.all_members.update(self.properties_dict)
        self.subexprs = []
        self.subexprs_dict = {}

        self.expr_names = {}  # mapping from parser expression context to member names

    def expr_name(self, ctx):
        return self.expr_names[ctx]

    def set_expr_name(self, ctx, name):
        self.expr_names[ctx] = name

    def declareZ3Constructor(self, type_ctx):
        arguments = []
        for id in self.params+self.public_members+self.private_members+self.properties+self.subexprs:
            arguments.append((id.name, type_ctx(id.type)))
        type_ctx(self.name).declare(f'{self.name}', *arguments)

    def show(self, z3_instance):
        for i, id in enumerate(self.getDeclaredMemberNames()):
            print(f'{id.name:>20s} : {z3_instance.arg(i)}')

    def getMemberNames(self):
        return [id.name for id in self.params+self.public_members+self.private_members+self.properties+self.subexprs]

    def getDeclaredMemberNames(self):
        return [id.name for id in self.params+self.public_members+self.private_members]

    def getDeclaredMemberValues(self, z3_instance):
        def pretty(s: str):
            import re
            event = re.findall(r'event\((.+)\)', s)
            if event:
                return f'[{event[0]}]'  # .replace('unit', '()')
            return s.replace('nothing', '[]')
        return [pretty(f'{z3_instance.arg(i)}') for i in
                     range(len(self.getDeclaredMemberNames()))]

    def getMemberValues(self, z3_instance):
        def pretty(s: str):
            import re
            event = re.findall(r'event\((.+)\)', s)
            if event:
                return f'[{event[0]}]'  # .replace('unit', '()')
            return s.replace('nothing', '[]')
        return [pretty(f'{z3_instance.arg(i)}') for i in
                range(len(self.getMemberNames()))]

    def getParamType(self, i):
        return self.params[i].type

    def getPublicMemberType(self, name):
        return self.public_members_dict[name]

    def getPrivateMemberType(self, name):
        return self.private_members_dict[name]

    def getSubExprType(self, name):
        return self.subexprs_dict[name]

    def getType(self, name):
        if name in self.all_members:
            return self.all_members[name]
        raise Exception(f"Unknown member {name}")

    def hasMember(self, name):
        return name in self.getMemberNames()

    def addSubExpr(self, expr, type_):
        name = self.expr_name(expr)  # it will always have been defined
        self.subexprs.append(TypedIdentifier(name, type_))
        self.subexprs_dict[name] = type_
        self.all_members[name] = type_
        self.expr_names[expr] = name

    def __str__(self):
        return self.name

    def __repr__(self):
        def indented_typed_identifiers(id_list):
            return '\n                '.join((f'{id.name} : {id.type}' for id in id_list))

        return f'''reactor {self.name}
    params:     {indented_typed_identifiers(self.params)}
    members:    {indented_typed_identifiers(self.public_members)}
    private:    {indented_typed_identifiers(self.private_members)}
    properties: {indented_typed_identifiers(self.properties)}
    subexprs:   {indented_typed_identifiers(self.subexprs)}
'''


class StructType:
    def __init__(self, ctx: ThoriumParser.StructContext,
                       name: str,
                       members: List[TypedIdentifier]):
        self.ctx = ctx
        self.name = name
        self.members = members
        self.members_dict = {m.name: m.type for m in members}
        self.z3_types = None

    def declareZ3Constructor(self, z3_types):
        self.z3_types = z3_types
        arguments = [(id.name, z3_types(id.type)) for id in self.members]
        z3_types(self.name).declare(f'{self.name}', *arguments)

    def getPublicMemberType(self, name):
        return self.members_dict[name]

    def __call__(self, *args):
        f = self.z3_types(self.name).__getattribute__(self.name)
        return f(*args)

    def __str__(self):
        return self.name

    def __repr__(self):
        def indented_typed_identifiers(id_list):
            return '\n             '.join((f'{id.name} : {id.type}' for id in id_list))

        return f'''struct {self.name}
    members: {indented_typed_identifiers(self.members)}
'''


class Z3Types:
    def __init__(self):
        unit = z3.Datatype('unit')
        unit.declare('unit')
        unit = unit.create()
        self.types = {'int': z3.IntSort(),
                      'real': z3.RealSort(),
                      'bool': z3.BoolSort(),
                      'unit': unit}
        self.datatypes = []
        self.addDatatype(Stream('int'))
        self.addDatatype(Stream('real'))
        self.addDatatype(Stream('bool'))
        self.addDatatype(Stream('unit'))

    def addDatatype(self, datatype):
        self.datatypes.append(datatype)
        self.types[str(datatype)] = z3.Datatype(str(datatype))
        if not isinstance(datatype, Stream):
            self.addDatatype(Stream(datatype.name))

    def __call__(self, type_):
        if isinstance(type_, Cell):
            return self.types[str(type_.type)]
        return self.types[str(type_)]

    def finalizeDatatypes(self):
        for datatype in self.datatypes:
            datatype.declareZ3Constructor(self)
        datatype_names = [str(dt) for dt in self.datatypes]
        args = [self(name) for name in datatype_names]
        datatypes = z3.CreateDatatypes(*args)
        self.types.update(
            {name: datatype for name, datatype in zip(datatype_names, datatypes)})


class Declarations(ThoriumVisitor):
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
        if not sub:   # todo: move to param list
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
            self.set_expr_name(sub, f'{self.expr_name(ctx)}-{i+1}')
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

    def visitLtlGlobally(self, ctx: ThoriumParser.LtlGloballyContext):
        self.visitSubExpr(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlEventually(self, ctx: ThoriumParser.LtlEventuallyContext):
        self.visitSubExpr(ctx, ctx.ltlProperty())
        return Cell('bool')

    def visitLtlUntil(self, ctx: ThoriumParser.LtlUntilContext):
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


class ReactiveValue:
    def __init__(self, trace, accessor, thorium_type, z3_type):
        self.trace = trace
        self.accessor = accessor
        self.thorium_type = thorium_type
        self.z3_type = z3_type

    def __call__(self, k):
        return self.accessor(self.trace(k))

    def isStream(self):
        return isinstance(self.thorium_type, Stream)

    def isNothing(self, k):
        if self.isStream():
            return self(k) == self.z3_type.nothing
        return False

    def isTrue(self, k):
        if self.isStream():
            return z3.If(self.isNothing(k), False, self.getValue(k))
        return self(k)

    def setValue(self, k, value):
        if self.isStream():
            return self(k) == self.z3_type.event(value)
        return self(k) == value

    def getValue(self, k, snapshot=False):
        if self.thorium_type == Stream('unit'):
            return z3.Not(self.isNothing(k))
        if self.isStream():
            return self.z3_type.value(self(k))
        if snapshot:
            return self(k-1)
        return self(k)

    #def __repr__(self):
        #return f'{self.accessor}:{self.thorium_type}({self.z3_type})'


class ReactorDefiner(ThoriumVisitor):
    def __init__(self, composite_types: dict, functions: dict, z3_types: Z3Types):
        ThoriumVisitor.__init__(self)
        self.solver = None
        self.trace = None
        self.reactor_type = None
        self.first_state = None
        self.k0 = None
        self.final_state = None
        self.composite_types = composite_types
        self.functions = functions
        self.z3_types = z3_types

        self.snapshot_trigger = False

        self.unary_operators = {'-': operator.neg,
                                'not': operator.not_}
        self.operators = {'+': operator.add,
                          '-': operator.sub,
                          '*': operator.mul,
                          '/': operator.truediv,
                          '<': operator.lt,
                          '<=': operator.le,
                          '>': operator.gt,
                          '>=': operator.ge,
                          '==': operator.eq,
                          '!=': operator.ne,
                          '->': z3.Implies,
                          'and': z3.And,
                          'or': z3.Or,
                          }

    def expr_name(self, ctx):
        return self.reactor_type.expr_name(ctx)

    def all_states(self):
        return range(self.first_state, self.final_state+1)

    def streaming_states(self):
        return range(self.first_state+1, self.final_state+1)

    def Assert(self, statement):
        self.solver.add(statement)

    def apply(self, f: callable,
                    args: List[ReactiveValue],
                    result: ReactiveValue):
        stream_args = [arg for arg in args if arg.isStream()]
        if stream_args:
            self.Assert(result.isNothing(self.first_state))
            for k in self.streaming_states():
                missing_args = z3.Or(*[arg.isNothing(k) for arg in stream_args])
                values = [arg.getValue(k, True) for arg in args]
                self.Assert(z3.If(missing_args,
                                  result.isNothing(k),
                                  result.setValue(k, f(*values))))
        else:
            for k in self.all_states():
                values = [arg.getValue(k) for arg in args]
                self.Assert(result.setValue(k, f(*values)))

    def __call__(self, name: str, typename: str, first_state: int, final_state: int, solver: z3.Solver):
        self.reactor_type = self.composite_types[typename]
        self.z3_reactor_type = self.z3_types(typename)
        self.trace = z3.Function(name, z3.IntSort(), self.z3_reactor_type)
        self.first_state = first_state
        self.k0 = first_state
        self.final_state = final_state
        self.solver = solver
        self.visit(self.reactor_type.ctx)
        return self.trace

    def visitReactor(self, ctx: ThoriumParser.ReactorContext):
        self.visitChildren(ctx)

    def visitMemberAccess(self, ctx: ThoriumParser.MemberAccessContext):
        result = self[self.expr_name(ctx)]
        composite = self[self.expr_name(ctx.expr())]
        accessor = composite.z3_type.__getattribute__(ctx.ID().getText())
        if composite.isStream():
            self.Assert(result.isNothing(self.first_state))
            for k in self.streaming_states():
                self.Assert(z3.If(composite.isNothing(k),
                                  result.isNothing(k),
                                  result.setValue(k, accessor(composite.getValue(k)))))
        else:
            for k in self.all_states():
                self.Assert(result(k) == accessor(composite(k)))
        self.visit(ctx.expr())

    def visitId(self, ctx: ThoriumParser.IdContext):
        id = self[ctx.ID().getText()]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(result(k) == id(k))
        self.visitChildren(ctx)

    def visitNumber(self, ctx: ThoriumParser.NumberContext):
        value = int(ctx.NUMBER().getText())
        accessor = self.z3_reactor_type.__getattribute__(self.expr_name(ctx))
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(accessor(self.trace(k)) == value)
        self.visitChildren(ctx)

    def __getitem__(self, id: str):
        if self.reactor_type.hasMember(id):
            thorium_type = self.reactor_type.getType(id)
            return ReactiveValue(self.trace,
                                 self.z3_reactor_type.__getattribute__(id),
                                 thorium_type,
                                 self.z3_types(thorium_type))
        elif id in self.functions:
            f = self.functions[id]
            f.setSolver(self.solver)
            return f
        elif id in self.composite_types:
            f = self.composite_types[id]
            if isinstance(f, StructType):
                return f

    def visitApply(self, ctx: ThoriumParser.ApplyContext):
        function = self[ctx.ID().getText()]
        args = [self[self.expr_name(expr)] for expr in ctx.expr()]
        result = self[self.expr_name(ctx)]
        self.apply(function, args, result)
        self.visitChildren(ctx)

    def visitLtlNegation(self, ctx: ThoriumParser.LtlNegationContext):
        arg = self[self.expr_name(ctx.ltlProperty())]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(result.setValue(k, z3.Not(arg.isTrue(k))))
        self.visitChildren(ctx)

    def globally(self, result, arg):
        for k in self.all_states()
            self.Assert(result(k) == z3.And(arg.isTrue(k), result(k+1)))
        self.Assert(result(self.final_state+1) == True)  # optimistic semantics

    def visitLtlGlobally(self, ctx: ThoriumParser.LtlGloballyContext):
        result,arg = self.getRVs(ctx,ctx.ltlProperty())
        self.globally(result, arg)
        self.visitChildren(ctx)

    def visitLtlEventually(self, ctx: ThoriumParser.LtlEventuallyContext):
        arg = self[self.expr_name(ctx.ltlProperty())]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(result.setValue(k, z3.Or(arg.isTrue(k), result.getValue(k+1))))
        self.solver.add(result.setValue(self.final_state+1, True))  # optimistic semantics
        self.visitChildren(ctx)

    def visitLtlUntil(self, ctx: ThoriumParser.LtlUntilContext):
        arg0 = self[self.expr_name(ctx.ltlProperty(0))]
        arg1 = self[self.expr_name(ctx.ltlProperty(1))]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(result.setValue(k, z3.Or(arg1.isTrue(k), z3.And(arg0.isTrue(k), result.getValue(k+1)))))
        self.solver.add(result.setValue(self.final_state+1, True))  # optimistic semantics
        self.visitChildren(ctx)

    def visitLtlParen(self, ctx: ThoriumParser.LtlParenContext):
        self.visitChildren(ctx)

    def visitLtlAnd(self, ctx: ThoriumParser.LtlAndContext):
        arg0 = self[self.expr_name(ctx.ltlProperty(0))]
        arg1 = self[self.expr_name(ctx.ltlProperty(1))]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(z3.If(z3.Or(arg0.isNothing(k), arg1.isNothing(k)),
                                  result.setValue(k, False),
                                  result.setValue(k, z3.And(arg0.getValue(k), arg1.getValue(k)))))
        self.visitChildren(ctx)

    def visitLtlImplication(self, ctx: ThoriumParser.LtlImplicationContext):
        arg0 = self[self.expr_name(ctx.ltlProperty(0))]
        arg1 = self[self.expr_name(ctx.ltlProperty(1))]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(z3.If(arg0.isNothing(k),
                                  result.setValue(k, True),
                                  result.setValue(k, z3.Implies(arg0.getValue(k), arg1.getValue(k)))))
        self.visitChildren(ctx)

    def unaryOp(self, ctx):
        f = self.unary_operators[ctx.op.text]
        arg0 = self[self.expr_name(ctx.expr())]
        result = self[self.expr_name(ctx)]
        self.apply(f, [arg0], result)

    def binOp(self, ctx):
        f = self.operators[ctx.op.text]
        arg0 = self[self.expr_name(ctx.expr(0))]
        arg1 = self[self.expr_name(ctx.expr(1))]
        result = self[self.expr_name(ctx)]
        self.apply(f, [arg0, arg1], result)

    def visitNegative(self, ctx: ThoriumParser.NegativeContext):
        self.unaryOp(ctx)
        self.visitChildren(ctx)

    def visitChanges(self, ctx: ThoriumParser.ChangesContext):
        expr = self[self.expr_name(ctx.expr())]
        result = self[self.expr_name(ctx)]
        self.solver.add(result.isNothing(self.first_state))
        for k in range(self.first_state+1, self.final_state+1):
            self.solver.add(z3.If(expr.getValue(k) != expr.getValue(k-1),
                                  result.setValue(k, expr.getValue(k)),
                                  result.isNothing(k)))
        self.visitChildren(ctx)

    def visitMult(self, ctx: ThoriumParser.MultContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitAdd(self, ctx: ThoriumParser.AddContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitCompare(self, ctx: ThoriumParser.CompareContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitEquals(self, ctx: ThoriumParser.EqualsContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitNot(self, ctx: ThoriumParser.NotContext):
        if self.snapshot_trigger:
            arg = self[self.expr_name(ctx.expr())]
            result = self[self.expr_name(ctx)]
            for k in range(self.first_state, self.final_state+1):
                self.solver.add(arg.isNothing(k),
                                result.setValue(k, True),
                                result.isNothing(k))
        else:
            self.unaryOp(ctx)
        self.visitChildren(ctx)

    def visitAnd(self, ctx: ThoriumParser.AndContext):
        if self.snapshot_trigger:
            arg0 = self[self.expr_name(ctx.expr(0))]
            arg1 = self[self.expr_name(ctx.expr(1))]
            result = self[self.expr_name(ctx)]
            for k in range(self.first_state, self.final_state+1):
                self.solver.add(z3.If(z3.Or(arg0.isNothing(k), arg1.isNothing(k)),
                                      result.isNothing(k),
                                      result.setValue(k, True)))

        else:
            self.binOp(ctx)
        self.visitChildren(ctx)

    def visitImplication(self, ctx: ThoriumParser.ImplicationContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitOr(self, ctx: ThoriumParser.AndContext):
        if self.snapshot_trigger:
            arg0 = self[self.expr_name(ctx.expr(0))]
            arg1 = self[self.expr_name(ctx.expr(1))]
            result = self[self.expr_name(ctx)]
            for k in range(self.first_state, self.final_state+1):
                self.solver.add(z3.If(z3.And(arg0.isNothing(k), arg1.isNothing(k)),
                                      result.isNothing(k),
                                      result.setValue(k, True)))

        else:
            self.binOp(ctx)
        self.visitChildren(ctx)

    def snapshot(self, result, cell, stream):
        self.Assert(result.isNothing(self.k0))
        for k in self.streaming_states():
            self.Assert(z3.If(stream.isNothing(k),
                              result.isNothing(k),
                              result.setValue(k, cell(k-1))))

    def visitSnapshot(self, ctx: ThoriumParser.SnapshotContext):
        result,(cell,stream) = self.getRVs(ctx,ctx.expr())
        self.snapshot(result, cell, stream)

        self.visit(ctx.expr(0))
        self.snapshot_trigger = True
        self.visit(ctx.expr(1))
        self.snapshot_trigger = False

    def merge(self, result, s1, s2):
        for k in range(self.first_state, self.final_state+1):
            self.Assert(result(k) == z3.If(s1.isNothing(k),
                                           s2(k),
                                           s1(k)))

    def visitMerge(self, ctx: ThoriumParser.MergeContext):
        result,(s1,s2) = self.getRVs(ctx,ctx.expr())
        self.merge(result, s1, s2)
        self.visitChildren(ctx)

    def filter(self, result, value, condition):
        for k in self.all_states():
            self.Assert(z3.If(condition.isNothing(k),
                              result.isNothing(k),
                              z3.If(condition.getValue(k, True),
                                    result.setValue(k, value.getValue(k)),
                                    result.isNothing(k))))

    def visitFilter(self, ctx: ThoriumParser.FilterContext):
        result,(value,condition) = self.getRVs(ctx,ctx.expr())
        self.filter(result, value, condition)
        self.visitChildren(ctx)

    def getRVs(self,*args):
        for arg in args:
            if isinstance(arg, list) or isinstance(arg, tuple):
                yield self.getRVs(*arg)
            else:
                yield self[self.expr_name(arg)]

    def hold(self, result, init, update):
        self.Assert(result(self.k0) == init(self.k0))
        for k in self.streaming_states():
            self.Assert(result(k) == z3.If(update.isNothing(k),
                                           result(k-1),
                                           update.getValue(k)))

    def visitHold(self, ctx: ThoriumParser.HoldContext):
        result,(init,update) = self.getRVs(ctx,ctx.expr())
        self.hold(result, init, update)
        self.visitChildren(ctx)


def parse_thorium_file(filename):
    input_stream = antlr4.FileStream(filename)
    lexer = ThoriumLexer(input_stream)
    stream = antlr4.CommonTokenStream(lexer)
    parser = ThoriumParser(stream)
    tree = parser.prog()

    declarations = Declarations().visitProg(tree)
    SubExprTypeCheck({t.name: t for t in declarations}).visitProg(tree)
    z3_types = Z3Types()
    composite_types = []
    functions = []
    for declaration in declarations:
        if isinstance(declaration, Function):
            functions.append(declaration)
        else:
            z3_types.addDatatype(declaration)
            composite_types.append(declaration)
    composite_types = {t.name: t for t in composite_types}
    z3_types.finalizeDatatypes()
    for f in functions:
        f.setTypeContext(z3_types)
    functions = {f.name: f for f in functions}

    return composite_types, functions, z3_types


def main(_argv):

    argparser = argparse.ArgumentParser(prog='thorium-verifier',
                                        description='Verifies reactor properties.')

    argparser.add_argument('filename')
    argparser.add_argument('-r', '--reactor', dest='reactor')
    argparser.add_argument('-p', '--property', dest='property')
    argparser.add_argument('-n', '--num-states', dest='N', type=int)
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
        for k in range(args.N+1):
            if k in f:
                trace.append(getter(f[k]))
            else:
                trace.append(getter(z3_trace.else_value()))

        trace = [namegetter()] + trace
        column_widths = [max([len(name) for name in column]) for column in trace]
        format_string = ' & '.join(('%%%ds' % width) for width in column_widths) + r' \\'
        print(r'\begin{centering}')
        print(r'\begin{tabular}[%s]' % ('|c'*len(column_widths)+'|'))
        print(r'\hline')
        print(format_string % tuple(['k']+ list(range(len(column_widths)-1))))
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
