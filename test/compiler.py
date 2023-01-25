#!/usr/bin/env python3
import argparse
import operator
import functools
import z3
import antlr4
from thorium import *
from typing import List

def lmap(f,iterable):
    return list(map(f,iterable))

class Cell:
    def __init__(self, type):
        if isinstance(type, Stream) or isinstance(type, Cell):
            self.type = type.type
        else:
            self.type = type

    def __str__(self):
        return f'cell-{self.type}'

    def __repr__(self):
        return f'cell-{self.type}'

class Stream:
    def __init__(self, type):
        if isinstance(type, Stream) or isinstance(type, Cell):
            self.type = type.type
        else:
            self.type = type
        self.name = self

    def declareZ3Constructor(self, type_ctx):
        type_ctx(self).declare('event', ('value',type_ctx(self.type)))
        type_ctx(self).declare('nothing')

    def __str__(self):
        return f'stream-{self.type}'

    def __repr__(self):
        return f'stream-{self.type}'

    def __eq__(self, other):
        return isinstance(other, Stream) and (self.type == other.type)


class TypedIdentifier:
    def __init__(self, name, type):
        self.name = name
        self.type = type

    def __repr__(self):
        return f'{self.name} : {self.type}'


class Function(ThoriumVisitor):
    def __init__(self, ctx:ThoriumParser.FunctionContext):
        self.visit(ctx)
        self.solver = None
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

    def unaryOp(self, ctx):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {f} {ctx.expr().member_name}')
        f = self.unary_operators[ctx.op.text]
        arg = self.visit(ctx.expr())
        return f(arg)

    def binOp(self, ctx):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.expr(0).member_name} {f} {ctx.expr(1).member_name}')
        f = self.operators[ctx.op.text]
        arg0 = self.visit(ctx.expr(0))
        arg1 = self.visit(ctx.expr(1))
        return f(arg0,arg1)

    def setSolver(self, solver):
        self.solver = solver

    def __call__(self, *args):
        self.symbols = {p.name: a for p, a in zip(self.params, args)}
        self.symbols['result'] = self.f(*args)
        self.visit(self.properties)
        return self.f(*args)

    def visitFunction(self, ctx:ThoriumParser.FunctionContext):
        self.name = ctx.ID().getText()
        self.params = self.visit(ctx.functionParams())
        self.result_type = self.visit(ctx.type_())
        self.properties = ctx.functionProperties()

    def setTypeContext(self, z3_types):
        args = [self.name] + [z3_types(param.type) for param in self.params] + [z3_types(self.result_type)]
        self.f = z3.Function(*args)

    def visitFunctionParams(self, ctx:ThoriumParser.FunctionParamsContext):
        return [self.visit(param) for param in ctx.functionParam()]

    def visitFunctionParam(self, ctx:ThoriumParser.FunctionParamContext):
        return TypedIdentifier(ctx.ID().getText(), self.visit(ctx.type_()))

    def visitType(self, ctx:ThoriumParser.TypeContext):
        return ctx.ID().getText()

    def visitFunctionProperty(self, ctx:ThoriumParser.FunctionPropertyContext):
        self.solver.add(self.visit(ctx.expr()))

    def visitId(self, ctx:ThoriumParser.IdContext):
        return self.symbols[ctx.ID().getText()]

    def visitNumber(self, ctx:ThoriumParser.NumberContext):
        return int(ctx.NUMBER().getText())

    def visitParen(self, ctx:ThoriumParser.ParenContext):
        return self.visit(ctx.expr())


    def visitMult(self, ctx:ThoriumParser.MultContext):
        return self.binOp(ctx)

    def visitAdd(self, ctx:ThoriumParser.AddContext):
        return self.binOp(ctx)

    def visitCompare(self, ctx:ThoriumParser.CompareContext):
        return self.binOp(ctx)

    def visitEquals(self, ctx:ThoriumParser.EqualsContext):
        return self.binOp(ctx)

    def visitNot(self, ctx:ThoriumParser.NotContext):
        return self.unaryOp(ctx)

    def visitAnd(self, ctx:ThoriumParser.AndContext):
        return self.binOp(ctx)

    def visitOr(self, ctx:ThoriumParser.AndContext):
        return self.binOp(ctx)

    def visitImplication(self, ctx:ThoriumParser.ImplicationContext):
        return self.binOp(ctx)

class ReactorType:
    def __init__(self, ctx:ThoriumParser.ReactorContext,
                       name: str,
                       params: List[TypedIdentifier],
                       public_members: List[TypedIdentifier],
                       private_members: List[TypedIdentifier],
                       properties: List[TypedIdentifier]):
        self.ctx = ctx
        self.name = name
        self.params = params
        self.params_dict = {m.name:m.type for m in params}
        self.public_members = public_members
        self.public_members_dict = {m.name:m.type for m in public_members}
        self.private_members = private_members
        self.private_members_dict = {m.name:m.type for m in private_members}
        self.properties = properties
        self.properties_dict = {m.name:m.type for m in properties}
        self.subexprs = []
        self.subexprs_dict = {}

    def declareZ3Constructor(self, type_ctx):
        arguments = []
        for id in self.params+self.public_members+self.private_members+self.properties+self.subexprs:
            arguments.append((id.name, type_ctx(id.type)))
        #arguments = [(id.name,type_ctx(id.type)) for id in self.params+self.public_members+self.private_members+self.subexprs]
        type_ctx(self.name).declare(f'{self.name}', *arguments)

    def show(self, z3_instance):
        for i,id in enumerate(self.params+self.public_members+self.private_members):#+self.properties):#+self.subexprs):
            print(f'{id.name:>20s} : {z3_instance.arg(i)}')

    def getMemberNames(self):
        return [id.name for id in self.params+self.public_members+self.private_members+self.properties+self.subexprs]

    def getDeclaredMemberNames(self):
        return [id.name for id in self.params+self.public_members+self.private_members]
        #return [id.name for id in self.params+self.public_members+self.private_members+self.properties+self.subexprs]

    def getDeclaredMemberValues(self, z3_instance):
        def pretty(s: str):
            import re
            #eventMatch = re.findall(r'event\(([^\)]+)\)',s)
            eventMatch = re.findall(r'event\((.+)\)',s)
            if eventMatch: return f'[{eventMatch[0]}]'#.replace('unit','()')
            return s.replace('nothing','[]')
        return [pretty(f'{z3_instance.arg(i)}') for i in
                     range(len(self.getDeclaredMemberNames()))]

    def getParamType(self, i):
        return self.params[i].type

    def getPublicMemberType(self, name):
        return self.public_members_dict[name]

    def getPrivateMemberType(self, name):
        return self.private_members_dict[name]

    def getSubExprType(self, name):
        return self.subexprs_dict[name]

    def getType(self,name):
        if name in self.public_members_dict: return self.public_members_dict[name]
        if name in self.private_members_dict: return self.private_members_dict[name]
        if name in self.params_dict: return self.params_dict[name]
        if name in self.properties_dict: return self.properties_dict[name]
        if name in self.subexprs_dict: return self.subexprs_dict[name]
        raise Exception(f"Unknown member {name}")

    def hasMember(self,name):
        return name in self.getMemberNames()

    def addSubExpr(self,expr):
        self.subexprs.append(TypedIdentifier(expr.member_name,expr.thorium_type))
        self.subexprs_dict[expr.member_name] = expr.thorium_type

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
    def __init__(self, ctx:ThoriumParser.StructContext,
                       name: str,
                       members: List[TypedIdentifier]):
        self.ctx = ctx
        self.name = name
        self.members = members
        self.members_dict = {m.name:m.type for m in members}

    def declareZ3Constructor(self, z3_types):
        self.z3_types = z3_types
        arguments = [(id.name, z3_types(id.type)) for id in self.members]
        z3_types(self.name).declare(f'{self.name}', *arguments)

    def getPublicMemberType(self, name):
        return self.members[name]

    def __call__(self, *args):
        f = self.z3_types(self.name).__getattribute__(self.name)
        #print(f'calling struct constructor {f} {args}')
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
        self.types = {'int':z3.IntSort(),
                      'real':z3.RealSort(),
                      'bool':z3.BoolSort(),
                      'unit':unit}
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
        if isinstance(type_,Cell):
            return self.types[str(type_.type)]
        return self.types[str(type_)]

    def finalizeDatatypes(self):
        for datatype in self.datatypes:
            #print(f'finalizing datatype {datatype}')
            datatype.declareZ3Constructor(self)
        datatype_names = [str(dt) for dt in self.datatypes]
        args = [self(name) for name in datatype_names]
        datatypes = z3.CreateDatatypes(*args)
        self.types.update(
            {name:datatype for name,datatype in zip(datatype_names, datatypes)})

def nonNone(l):
    return [i for i in l if i!=None]

class Declarations(ThoriumVisitor):
    def visitProg(self, ctx:ThoriumParser.ProgContext):
        return nonNone(lmap(self.visit, ctx.decl()))

    def visitDecl(self, ctx:ThoriumParser.DeclContext):
        if ctx.enum(): return self.visit(ctx.enum())
        if ctx.struct(): return self.visit(ctx.struct())
        if ctx.reactor(): return self.visit(ctx.reactor())
        if ctx.function(): return self.visit(ctx.function())

    def visitFunction(self, ctx:ThoriumParser.FunctionContext):
        return Function(ctx)

    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        return ReactorType(ctx,
                           ctx.ID().getText(),
                           self.visitOrDefault(ctx.reactorParams(),[]),
                           self.visitOrDefault(ctx.reactorMembers(0),[]),
                           self.visitOrDefault(ctx.reactorMembers(1),[]),
                           self.visitOrDefault(ctx.reactorProperties(),[]))

    def visitStruct(self, ctx:ThoriumParser.ReactorContext):
        return StructType(ctx,
                          ctx.ID().getText(),
                          self.visitOrDefault(ctx.structMembers(),[]))

    def visitOrDefault(self,node,default):
        if node:
            return self.visit(node)
        return default

    def visitReactiveType(self, ctx:ThoriumParser.ReactiveTypeContext):
        if ctx.CELL():
            return Cell(self.visit(ctx.type_()))
        return Stream(self.visit(ctx.type_()))

    def visitType(self, ctx:ThoriumParser.TypeContext):
        return ctx.ID().getText()

    def visitReactorParams(self, ctx:ThoriumParser.ReactorParamsContext):
        return lmap(self.visit, ctx.reactorParam())

    def visitReactorParam(self, ctx:ThoriumParser.ReactorParamContext):
        return TypedIdentifier(ctx.ID().getText(), self.visit(ctx.reactiveType()))

    def visitStructMembers(self, ctx:ThoriumParser.StructMembersContext):
        return lmap(self.visit, ctx.structMember())

    def visitStructMember(self, ctx:ThoriumParser.StructMemberContext):
        return TypedIdentifier(ctx.ID().getText(), self.visit(ctx.type_()))

    def visitReactorMembers(self, ctx:ThoriumParser.ReactorMembersContext):
        return lmap(self.visit, ctx.reactorMember())

    def visitReactorMember(self, ctx:ThoriumParser.ReactorMemberContext):
        return TypedIdentifier(ctx.ID().getText(), self.visit(ctx.reactiveType()))

    def visitReactorProperties(self, ctx:ThoriumParser.ReactorPropertiesContext):
        return lmap(self.visit, ctx.reactorProperty())

    def visitReactorProperty(self, ctx:ThoriumParser.ReactorPropertyContext):
        return TypedIdentifier(ctx.ID().getText(), Cell('bool'))


def hasStreamType(types):
    for type in types:
        if isinstance(type,Stream):
            return True
    return False


class SubExprTypeCheck(ThoriumVisitor):
    def __init__(self, decls):
        self.decls = decls

    def visitFunction(self, ctx:ThoriumParser.FunctionContext):
        pass # todo: implement type checking

    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        self.reactor = self.decls[ctx.ID().getText()]
        for m in ctx.reactorMembers(): self.visit(m)
        if ctx.reactorProperties():
            self.visit(ctx.reactorProperties())

    def visitReactorMember(self, ctx:ThoriumParser.ReactorMemberContext):
        ctx.expr().member_name = ctx.ID().getText()
        ctx.expr().thorium_type = self.visit(ctx.expr())

    def visitReactorProperty(self, ctx:ThoriumParser.ReactorPropertyContext):
        #print(f'visitReactorProperty: {ctx.ID()}')
        ctx.property_().member_name = ctx.ID().getText()
        ctx.property_().thorium_type = self.visit(ctx.property_())

    def visitProperty(self, ctx:ThoriumParser.PropertyContext):
        #print(f'visitProperty: {ctx.ltlProperty()}')
        if ctx.ltlProperty():
            ctx.ltlProperty().member_name = ctx.member_name
            ctx.ltlProperty().thorium_type = self.visit(ctx.ltlProperty())
            return ctx.ltlProperty().thorium_type

    def visitLtlNegation(self, ctx:ThoriumParser.LtlNegationContext):
        #print(f'visitLtlNegation: {ctx.ltlProperty()}')
        self.visitSubExpr(ctx,ctx.ltlProperty())
        return Cell('bool')

    def visitLtlParen(self, ctx:ThoriumParser.LtlParenContext):
        #print(f'visitLtlParen: {ctx.ltlProperty()}')
        ctx.ltlProperty().member_name = ctx.member_name
        return self.visit(ctx.ltlProperty())

    def visitLtlGlobally(self, ctx:ThoriumParser.LtlGloballyContext):
        #print(f'visitLtlGlobally: {ctx.ltlProperty()}')
        self.visitSubExpr(ctx,ctx.ltlProperty())
        return Cell('bool')

    def visitLtlEventually(self, ctx:ThoriumParser.LtlEventuallyContext):
        #print(f'visitLtlEventually: {ctx.ltlProperty()}')
        self.visitSubExpr(ctx,ctx.ltlProperty())
        return Cell('bool')

    def visitLtlUntil(self, ctx:ThoriumParser.LtlUntilContext):
        self.visitSubExprs(ctx,ctx.ltlProperty())
        return Cell('bool')

    def visitLtlAnd(self, ctx:ThoriumParser.LtlAndContext):
        self.visitSubExprs(ctx,ctx.ltlProperty())
        return Cell('bool')

    def visitLtlOr(self, ctx:ThoriumParser.LtlAndContext):
        self.visitSubExprs(ctx,ctx.ltlProperty())
        return Cell('bool')

    def visitLtlImplication(self, ctx:ThoriumParser.LtlImplicationContext):
        #print(f'visitLtlImplication: {ctx.ltlProperty()}')
        self.visitSubExprs(ctx,ctx.ltlProperty())
        return Cell('bool')

    def visitLtlExpr(self, ctx:ThoriumParser.LtlExprContext):
        #print(f'visitExpr: {ctx.expr()}')
        ctx.expr().member_name = ctx.member_name
        return self.visit(ctx.expr())

    def visitApply(self, ctx:ThoriumParser.ApplyContext):
        types = self.visitSubExprs(ctx)
        f = self.decls[ctx.ID().getText()]
        if isinstance(f,Function):
            result_type = f.result_type
        else: # struct, for now
            result_type = f.name
        if hasStreamType(types): return Stream(result_type)
        return result_type

    def visitNegative(self, ctx:ThoriumParser.NegativeContext):
        ctx.expr().member_name = f'{ctx.member_name}-1'
        ctx.expr().thorium_type = self.visit(ctx.expr())
        self.reactor.addSubExpr(ctx.expr())
        return ctx.expr().thorium_type

    def visitId(self, ctx:ThoriumParser.IdContext):
        id = ctx.ID().getText()
        return self.reactor.getType(id)

    def visitChanges(self, ctx:ThoriumParser.ChangesContext):
        ctx.expr().member_name = f'{ctx.member_name}-1'
        ctx.expr().thorium_type = self.visit(ctx.expr())
        self.reactor.addSubExpr(ctx.expr())
        return Stream(ctx.expr().thorium_type)

    def visitNumber(self, ctx:ThoriumParser.NumberContext):
        return 'int'

    def visitParen(self, ctx:ThoriumParser.ParenContext):
        ctx.expr().member_name = ctx.member_name
        return self.visit(ctx.expr())

    def visitSubExpr(self,ctx, sub=None):
        types = []
        if not sub: sub = ctx.expr()
        sub.member_name = f'{ctx.member_name}-1'
        sub.thorium_type = self.visit(sub)
        self.reactor.addSubExpr(sub)
        return sub.thorium_type

    def visitSubExprs(self,ctx, subs = None):
        types = []
        if not subs: subs = ctx.expr()
        for i,sub in enumerate(subs):
            sub.member_name = f'{ctx.member_name}-{i+1}'
            #print(f'visiting {sub.member_name} {type(sub)}')
            sub.thorium_type = self.visit(sub)
            types.append(sub.thorium_type)
            self.reactor.addSubExpr(sub)
        return types

    def visitMult(self, ctx:ThoriumParser.MultContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types): return Stream('int')
        return Cell('int')

    def visitAdd(self, ctx:ThoriumParser.AddContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types): return Stream('int')
        return Cell('int')

    def visitCompare(self, ctx:ThoriumParser.CompareContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types): return Stream('bool')
        return Cell('bool')

    def visitEquals(self, ctx:ThoriumParser.EqualsContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types): return Stream('bool')
        return Cell('bool')

    def visitNot(self, ctx:ThoriumParser.NotContext):
        type = self.visitSubExpr(ctx)
        if isinstance(type,Stream): return Stream('bool')
        return Cell('bool')

    def visitAnd(self, ctx:ThoriumParser.AndContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types): return Stream('bool')
        return Cell('bool')

    def visitOr(self, ctx:ThoriumParser.AndContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types): return Stream('bool')
        return Cell('bool')

    def visitImplication(self, ctx:ThoriumParser.ImplicationContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types): return Stream('bool')
        return Cell('bool')

    def visitFilter(self, ctx:ThoriumParser.FilterContext):
        valueType,conditionType = self.visitSubExprs(ctx)
        return Stream(valueType)

    def visitSnapshot(self, ctx:ThoriumParser.SnapshotContext):
        cellType,streamType = self.visitSubExprs(ctx)
        #TODO: typeCheck
        return Stream(cellType)

    def visitAlternate(self, ctx:ThoriumParser.AlternateContext):
        typeA,typeB = self.visitSubExprs(ctx)
        #TODO: typeCheck (both should be the same kind of stream)
        return typeA

    def visitHold(self, ctx:ThoriumParser.HoldContext):
        cellType,streamType = self.visitSubExprs(ctx)
        #TODO: typeCheck (both should hold the same kind of value)
        return Cell(cellType)


class ReactiveValue:
    def __init__(self, trace, accessor, thorium_type, z3_type):
        self.trace = trace
        self.accessor = accessor
        self.thorium_type = thorium_type
        self.z3_type = z3_type

    def __call__(self,k):
        return self.accessor(self.trace(k))

    def isStream(self):
        return isinstance(self.thorium_type,Stream)

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

    def __repr__(self):
        return f'{self.accessor}:{self.thorium_type}({self.z3_type})'


class ReactorDefiner(ThoriumVisitor):
    def __init__(self, composite_types:dict, functions:dict, z3_types:Z3Types):
        ThoriumVisitor.__init__(self)
        self.solver = None
        self.trace = None
        self.reactor_type = None
        self.first_state = None
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

    def all_states(self):
        return range(self.first_state, self.final_state+1)

    def active_states(self):
        return range(self.first_state+1, self.final_state+1)

    def Assert(self,statement):
        self.solver.add(statement)

    def apply(self, f: callable,
                    args: List[ReactiveValue],
                    result: ReactiveValue):
        stream_args = [arg for arg in args if arg.isStream()]
        if stream_args:
            self.Assert(result.isNothing(self.first_state))
            for k in self.active_states():
                missing_args = z3.Or(*[arg.isNothing(k) for arg in stream_args])
                values = [arg.getValue(k, True) for arg in args]
                self.solver.add(z3.If(missing_args,
                                      result.isNothing(k),
                                      result.setValue(k, f(*values))))
        else:
            for k in self.all_states():
                values = [arg.getValue(k) for arg in args]
                #print(f'apply: {result.setValue(k, f(*values))}')
                self.solver.add(result.setValue(k, f(*values)))

    def __call__(self, name: str, typename: str, first_state: int, final_state: int, solver: z3.Solver):
        self.reactor_type = self.composite_types[typename]
        self.z3_reactor_type = self.z3_types(typename)
        self.trace = z3.Function(name, z3.IntSort(), self.z3_reactor_type)
        self.first_state = first_state
        self.final_state = final_state
        self.solver = solver
        #print(f'calling run on ReactorDefiner with type: {self.reactor_type} {type(self.reactor_type)}')
        self.visit(self.reactor_type.ctx)
        return self.trace

    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        #print(f'ReactorDefiner visiting {ctx.ID()}')
        self.visitChildren(ctx)

    def visitId(self, ctx:ThoriumParser.IdContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.ID()}')
        id = self[ctx.ID().getText()]
        result = self[ctx.member_name]
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(result(k) == id(k))
        self.visitChildren(ctx)

    def visitNumber(self, ctx:ThoriumParser.NumberContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.NUMBER()}')
        value = int(ctx.NUMBER().getText())
        accessor = self.z3_reactor_type.__getattribute__(ctx.member_name)
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(accessor(self.trace(k)) == value)
        self.visitChildren(ctx)

    def __getitem__(self, id: str):
        if self.reactor_type.hasMember(id):
            thorium_type = self.reactor_type.getType(id)
            return ReactiveValue(self.trace,
                                 self.z3_reactor_type.__getattribute__(id),
                                 thorium_type,
                                 self.z3_types(thorium_type) )
        elif id in self.functions:
            f = self.functions[id]
            f.setSolver(self.solver)
            return f
        elif id in self.composite_types:
            f = self.composite_types[id]
            if isinstance(f,StructType):
                return f

    def visitApply(self, ctx:ThoriumParser.ApplyContext):
        function = self[ctx.ID().getText()]
        args = [self[expr.member_name] for expr in ctx.expr()]
        result = self[ctx.member_name]
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} {ctx.ID().getText()}({args})')
        self.apply(function, args, result)
        self.visitChildren(ctx)

    def visitLtlNegation(self, ctx:ThoriumParser.LtlNegationContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = not {ctx.ltlProperty().member_name}')
        arg = self[ctx.ltlProperty().member_name]
        result = self[ctx.member_name]
        #print(result.thorium_type)
        #print(arg.thorium_type)
        for k in range(self.first_state,self.final_state+1):
            self.solver.add(result.setValue(k, z3.Not(arg.isTrue(k))))
        self.visitChildren(ctx)


    def visitLtlGlobally(self, ctx:ThoriumParser.LtlGloballyContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = globally {ctx.ltlProperty().member_name}')
        arg = self[ctx.ltlProperty().member_name]
        result = self[ctx.member_name]
        for k in range(self.first_state,self.final_state+1):
            self.solver.add(result.setValue(k, z3.And(arg.isTrue(k), result.getValue(k+1))))
        self.solver.add(result.setValue(self.final_state+1, True)) # optimistic semantics
        self.visitChildren(ctx)

    def visitLtlEventually(self, ctx:ThoriumParser.LtlEventuallyContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = globally {ctx.ltlProperty().member_name}')
        arg = self[ctx.ltlProperty().member_name]
        result = self[ctx.member_name]
        for k in range(self.first_state,self.final_state+1):
            self.solver.add(result.setValue(k,z3.Or(arg.isTrue(k),result.getValue(k+1))))
        self.solver.add(result.setValue(self.final_state+1, True)) # optimistic semantics
        self.visitChildren(ctx)

    def visitLtlUntil(self, ctx:ThoriumParser.LtlUntilContext):
        arg0 = self[ctx.ltlProperty(0).member_name]
        arg1 = self[ctx.ltlProperty(1).member_name]
        result = self[ctx.member_name]
        for k in range(self.first_state,self.final_state+1):
            self.solver.add(result.setValue(k, z3.Or(arg1.isTrue(k),z3.And(arg0.isTrue(k),result.getValue(k+1)))))
        self.solver.add(result.setValue(self.final_state+1, True)) # optimistic semantics
        self.visitChildren(ctx)

    def visitLtlParen(self, ctx:ThoriumParser.LtlParenContext):
        #print(f'Reactor {self.reactor_type}, paren {ctx.ltlProperty().member_name} {type(ctx.ltlProperty())}')
        self.visitChildren(ctx)

    def visitLtlAnd(self, ctx:ThoriumParser.LtlAndContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.ltlProperty(0).member_name} and {ctx.ltlProperty(1).member_name}')
        arg0 = self[ctx.ltlProperty(0).member_name]
        arg1 = self[ctx.ltlProperty(1).member_name]
        result = self[ctx.member_name]
        for k in range(self.first_state,self.final_state+1):
            self.solver.add(z3.If(z3.Or(arg0.isNothing(k),arg1.isNothing(k)),
                                  result.setValue(k,False),
                                  result.setValue(k,z3.And(arg0.getValue(k),arg1.getValue(k)))))
        self.visitChildren(ctx)

    def visitLtlImplication(self, ctx:ThoriumParser.LtlImplicationContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.ltlProperty(0).member_name} -> {ctx.ltlProperty(1).member_name}')
        arg0 = self[ctx.ltlProperty(0).member_name]
        arg1 = self[ctx.ltlProperty(1).member_name]
        result = self[ctx.member_name]
        for k in range(self.first_state,self.final_state+1):
            self.solver.add(z3.If(arg0.isNothing(k),
                                  result.setValue(k,True),
                                  result.setValue(k,z3.Implies(arg0.getValue(k),arg1.getValue(k)))))
        self.visitChildren(ctx)

    def unaryOp(self, ctx):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {f} {ctx.expr().member_name}')
        f = self.unary_operators[ctx.op.text]
        arg0 = self[ctx.expr().member_name]
        result = self[ctx.member_name]
        self.apply(f, [arg0], result)

    def binOp(self, ctx):
        f = self.operators[ctx.op.text]
        arg0 = self[ctx.expr(0).member_name]
        arg1 = self[ctx.expr(1).member_name]
        result = self[ctx.member_name]
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.expr(0).member_name} {f} {ctx.expr(1).member_name}')
        #print(f'Reactor {self.reactor_type}, {result} = {arg0} {f} {arg1}')
        self.apply(f, [arg0, arg1], result)

    def visitNegative(self, ctx:ThoriumParser.NegativeContext):
        self.unaryOp(ctx)
        self.visitChildren(ctx)

    def visitChanges(self, ctx:ThoriumParser.ChangesContext):
        expr = self[ctx.expr().member_name]
        result = self[ctx.member_name]
        self.solver.add(result.isNothing(self.first_state))
        for k in range(self.first_state+1, self.final_state+1):
            self.solver.add(z3.If(expr.getValue(k) != expr.getValue(k-1),
                                  result.setValue(k,expr.getValue(k)),
                                  result.isNothing(k)))
        self.visitChildren(ctx)


    def visitMult(self, ctx:ThoriumParser.MultContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitAdd(self, ctx:ThoriumParser.AddContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitCompare(self, ctx:ThoriumParser.CompareContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitEquals(self, ctx:ThoriumParser.EqualsContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitNot(self, ctx:ThoriumParser.NotContext):
        if self.snapshot_trigger:
            arg = self[ctx.expr().member_name]
            result = self[ctx.member_name]
            for k in range(self.first_state, self.final_state+1):
                self.solver.add(arg.isNothing(),
                                result.setValue(k,True),
                                result.isNothing(k))
        else:
            self.unaryOp(ctx)
        self.visitChildren(ctx)

    def visitAnd(self, ctx:ThoriumParser.AndContext):
        if self.snapshot_trigger:
            arg0 = self[ctx.expr(0).member_name]
            arg1 = self[ctx.expr(1).member_name]
            result = self[ctx.member_name]
            #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.expr(0).member_name} and {ctx.expr(1).member_name} (snapshot trigger)')
            for k in range(self.first_state, self.final_state+1):
                self.solver.add(z3.If(z3.Or(arg0.isNothing(k),arg1.isNothing(k)),
                                      result.isNothing(k),
                                      result.setValue(k, True)))

        else:
            self.binOp(ctx)
        self.visitChildren(ctx)

    def visitImplication(self, ctx:ThoriumParser.ImplicationContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitOr(self, ctx:ThoriumParser.AndContext):
        if self.snapshot_trigger:
            arg0 = self[ctx.expr(0).member_name]
            arg1 = self[ctx.expr(1).member_name]
            result = self[ctx.member_name]
            for k in range(self.first_state, self.final_state+1):
                self.solver.add(z3.If(z3.And(arg0.isNothing(k),arg1.isNothing(k)),
                                      result.isNothing(k),
                                      result.setValue(k, True)))

        else:
            self.binOp(ctx)
        self.visitChildren(ctx)

    def visitSnapshot(self, ctx:ThoriumParser.SnapshotContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.expr(0).member_name} @ {ctx.expr(1).member_name}')
        cell = self[ctx.expr(0).member_name]
        stream = self[ctx.expr(1).member_name]
        result = self[ctx.member_name]

        self.solver.add(result.isNothing(self.first_state))
        for k in range(self.first_state+1, self.final_state+1):
            self.solver.add(z3.If(stream.isNothing(k),
                                  result.isNothing(k),
                                  result.setValue(k, cell.getValue(k-1))))
        self.visit(ctx.expr(0))
        self.snapshot_trigger = True
        self.visit(ctx.expr(1))
        self.snapshot_trigger = False

    def visitAlternate(self, ctx:ThoriumParser.AlternateContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.expr(0).member_name} | {ctx.expr(1).member_name}')
        altA = self[ctx.expr(0).member_name]
        altB = self[ctx.expr(1).member_name]
        result = self[ctx.member_name]
        for k in range(self.first_state,self.final_state+1):
            self.solver.add(result(k) == z3.If(altA.isNothing(k),
                                               altB(k),
                                               altA(k)))
        self.visitChildren(ctx)

    def visitFilter(self, ctx:ThoriumParser.FilterContext):
        value = self[ctx.expr(0).member_name]
        condition = self[ctx.expr(1).member_name]
        result = self[ctx.member_name]

        for k in range(self.first_state,self.final_state+1):
            self.solver.add(z3.If(condition.isNothing(k),
                                  result.isNothing(k),
                                  z3.If(condition.getValue(k, True),
                                        result.setValue(k, value.getValue(k)),
                                        result.isNothing(k))))
        self.visitChildren(ctx)

    def visitHold(self, ctx:ThoriumParser.HoldContext):
        #print(f'Reactor {self.reactor_type}, {ctx.member_name} = {ctx.expr(0).member_name} .. {ctx.expr(1).member_name}')
        init = self[ctx.expr(0).member_name]
        update = self[ctx.expr(1).member_name]
        result = self[ctx.member_name]
        #print(f'result {result} init {init}')
        self.solver.add(result(self.first_state) == init(self.first_state))
        for k in range(self.first_state+1, self.final_state+1):
            self.solver.add(result(k) == z3.If(update.isNothing(k),
                                               result(k-1),
                                               update.getValue(k)))
        self.visitChildren(ctx)


class PrintVisitor(ThoriumVisitor):
    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        params = self.visit(ctx.reactorParams())
        #print(f'params: {params}')
        members = [self.visit(m) for m in ctx.reactorMembers()]
        #print(f'members: {members}')

    def visitReactorParams(self, ctx:ThoriumParser.ReactorParamsContext):
        return [self.visit(m) for m in ctx.reactorParam()]

    def visitReactorMembers(self, ctx:ThoriumParser.ReactorMembersContext):
        return [self.visit(m) for m in ctx.reactorMember()]

    def visitReactorParam(self, ctx:ThoriumParser.ReactorParamContext):
        return ctx.ID().getText()

    def visitReactorMember(self, ctx:ThoriumParser.ReactorMemberContext):
        self.ExprName = ctx.ID().getText()
        #print(f'member {ctx.ID()} = {self.visit(ctx.expr())}')
        return ctx.ID().getText()

    def visitAdd(self, ctx:ThoriumParser.AddContext):
        OP = '+'
        if ctx.MINUS(): OP = '-'
        return [OP, self.visit(ctx.expr(0)), self.visit(ctx.expr(1))]

    # Visit a parse tree produced by ThoriumParser#number.
    def visitNumber(self, ctx:ThoriumParser.NumberContext):
        return ctx.NUMBER().getText()

    # Visit a parse tree produced by ThoriumParser#negative.
    def visitNegative(self, ctx:ThoriumParser.NegativeContext):
        return ["-", self.visit(ctx.expr())]

    # Visit a parse tree produced by ThoriumParser#paren.
    def visitParen(self, ctx:ThoriumParser.ParenContext):
        return self.visit(ctx.expr())

    # Visit a parse tree produced by ThoriumParser#mult.
    def visitMult(self, ctx:ThoriumParser.MultContext):
        OP = '*'
        if ctx.DIV(): OP = '/'
        return [OP, self.visit(ctx.expr(0)), self.visit(ctx.expr(1))]
        return self.visitChildren(ctx)

    def visitAnd(self, ctx:ThoriumParser.OrContext):
        return ['and', self.visit(ctx.expr(0)), self.visit(ctx.expr(1))]

    def visitOr(self, ctx:ThoriumParser.OrContext):
        return ['or', self.visit(ctx.expr(0)), self.visit(ctx.expr(1))]

    def visitAlternate(self, ctx:ThoriumParser.AlternateContext):
        return ['ALT', self.visit(ctx.expr(0)), self.visit(ctx.expr(1))]

    # Visit a parse tree produced by ThoriumParser#id.
    def visitId(self, ctx:ThoriumParser.IdContext):
        return ctx.ID().getText()

    # Visit a parse tree produced by ThoriumParser#snapshot.
    def visitSnapshot(self, ctx:ThoriumParser.SnapshotContext):
        return ['AT', self.visit(ctx.expr(0)), self.visit(ctx.expr(1))]

    # Visit a parse tree produced by ThoriumParser#hold.
    def visitHold(self, ctx:ThoriumParser.HoldContext):
        return ['HOLD', self.visit(ctx.expr(0)), self.visit(ctx.expr(1))]

def compile(filename):
    input_stream = antlr4.FileStream(filename)
    lexer = ThoriumLexer(input_stream)
    stream = antlr4.CommonTokenStream(lexer)
    parser = ThoriumParser(stream)
    tree = parser.prog();

    declarations = Declarations().visitProg(tree)
    SubExprTypeCheck({t.name:t for t in declarations}).visitProg(tree)
    z3_types = Z3Types()
    composite_types = []
    functions = []
    for declaration in declarations:
        if isinstance(declaration,Function):
            functions.append(declaration)
        else:
            z3_types.addDatatype(declaration)
            composite_types.append(declaration)
    composite_types = {t.name:t for t in composite_types}
    z3_types.finalizeDatatypes()
    for f in functions:
        f.setTypeContext(z3_types)
    functions = {f.name:f for f in functions}

    return composite_types, functions, z3_types


def main(argv):

    argparser = argparse.ArgumentParser(prog='thorium-verifier',
                                        description='Verifies reactor properties.')

    argparser.add_argument('filename')
    argparser.add_argument('-r', '--reactor', dest='reactor')
    argparser.add_argument('-p', '--property', dest='property')
    argparser.add_argument('-n', '--num-states', dest='N', type=int)

    args = argparser.parse_args()

    composite_types, functions, z3_types = compile(args.filename)


    #for t in composite_types.values():
    #    print(repr(t))

    #PrintVisitor().visitProg(tree)

    reactor_definer = ReactorDefiner(composite_types, functions, z3_types)
    solver = z3.Solver()
    reactor = reactor_definer(f'{args.reactor}-main', args.reactor, 0, args.N, solver)
    reactor_type = z3_types(args.reactor)
    thorium_reactor = composite_types[args.reactor]

    #print(repr(thorium_reactor))

    property = reactor_type.__getattribute__(args.property)

    solver.add(z3.Not(property(reactor(0))))

    verification_result = solver.check()
    if verification_result==z3.sat:
        #print(solver.model())
        z3_trace = solver.model()[reactor]
        f = {a.as_long():b for a,b in z3_trace.as_list()[:-1]}
        trace = []
        for k in range(args.N+1):
            if k in f:
                trace.append(thorium_reactor.getDeclaredMemberValues(f[k]))
            else:
                trace.append(thorium_reactor.getDeclaredMemberValues(z3_trace.else_value()))

        trace = [thorium_reactor.getDeclaredMemberNames()] + trace
        column_widths = [max([len(name) for name in column]) for column in trace]
        format_string = ' '.join('%%%ds'%width for width in column_widths)
        for row in [[t[i] for t in trace] for i in range(len(trace[0]))]:
            print(format_string%tuple(row))

    if verification_result==z3.unsat:
        print(f'Property "{args.property}" for reactor "{args.reactor}" holds for all runs of {args.N} steps.')

if __name__ == '__main__':
    main(sys.argv)
