#!/usr/bin/env python3

import sys
import z3
import antlr4
from thorium import *
from typing import List

def lmap(f,iterable):
    return list(map(f,iterable))

class Cell:
    def __init__(self, type):
        self.type = type

    def __str__(self):
        return f'cell-{self.type}'

    def __repr__(self):
        return f'cell-{self.type}'

class Stream:
    def __init__(self, type):
        self.type = type
        self.name = self

    def declareZ3Constructor(self, type_ctx):
        #type_ctx(self).declare(f'{self.type}-event', ('value',type_ctx(self.type)))
        #type_ctx(self).declare(f'{self.type}-nothing')
        type_ctx(self).declare('event', ('value',type_ctx(self.type)))
        type_ctx(self).declare('nothing')

    def __str__(self):
        return f'stream-{self.type}'

    def __repr__(self):
        return f'stream-{self.type}'

class TypedIdentifier:
    def __init__(self, name, type):
        self.name = name
        self.type = type

    def __repr__(self):
        return f'{self.name} : {self.type}'

class ReactorType:
    def __init__(self, ctx:ThoriumParser.ReactorContext,
                       name: str,
                       params: List[TypedIdentifier],
                       public_members: List[TypedIdentifier],
                       private_members: List[TypedIdentifier]):
        self.ctx = ctx
        self.name = name
        self.params = params
        self.params_dict = {m.name:m.type for m in params}
        self.public_members = public_members
        self.public_members_dict = {m.name:m.type for m in public_members}
        self.private_members = private_members
        self.private_members_dict = {m.name:m.type for m in private_members}
        self.subexprs = []
        self.subexprs_dict = {}

    def declareZ3Constructor(self, type_ctx):
        arguments = [(id.name,type_ctx(id.type)) for id in self.params+self.public_members+self.private_members+self.subexprs]
        type_ctx(self.name).declare(f'{self.name}', *arguments)

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
        raise Exception(f"Unknown member {name}")

    def addSubExpr(self,name,type):
        self.subexprs.append(TypedIdentifier(name,type))
        self.subexprs_dict[name] = type

    def __str__(self):
        return self.name

    def __repr__(self):
        def indented_typed_identifiers(id_list):
            return '\n             '.join((f'{id.name} : {id.type}' for id in id_list))

        return f'''reactor {self.name}
    params:  {indented_typed_identifiers(self.params)}
    members: {indented_typed_identifiers(self.public_members)}
    private: {indented_typed_identifiers(self.private_members)}
    subexprs: {indented_typed_identifiers(self.subexprs)}
'''

class StructType:
    def __init__(self, ctx:ThoriumParser.StructContext,
                       name: str,
                       members: List[TypedIdentifier]):
        self.ctx = ctx
        self.name = name
        self.members = members
        self.members_dict = {m.name:m.type for m in members}

    def declareZ3Constructor(self, type_ctx):
        arguments = [(id.name, type_ctx(id.type)) for id in self.members]
        type_ctx(self.name).declare(f'{self.name}', *arguments)

    def getPublicMemberType(self, name):
        return self.members[name]

    def __str__(self):
        return self.name

    def __repr__(self):
        def indented_typed_identifiers(id_list):
            return '\n             '.join((f'{id.name} : {id.type}' for id in id_list))

        return f'''struct {self.name}
    members: {indented_typed_identifiers(self.members)}
'''

class TypeContext:
    def __init__(self):
        unit = z3.Datatype('unit')
        unit.declare('unit')
        unit = unit.create()
        self.types = {'int':z3.IntSort(),
                      'real':z3.RealSort(),
                      'bool':z3.BoolSort(),
                      'unit':unit}
        self.Datatypes = []
        self.addDatatype(Stream('int'))
        self.addDatatype(Stream('real'))
        self.addDatatype(Stream('unit'))


    def addDatatype(self, datatype):
        self.Datatypes.append(datatype)
        self.types[str(datatype)] = z3.Datatype(str(datatype))
        if not isinstance(datatype, Stream):
            self.addDatatype(Stream(datatype.name))

    def __call__(self, type_):
        if isinstance(type_,Cell):
            return self.types[str(type_.type)]
        return self.types[str(type_)]

    def finalizeDatatypes(self):
        for datatype in self.Datatypes:
            datatype.declareZ3Constructor(self)
        datatype_names = [str(dt) for dt in self.Datatypes]
        args = [self(name) for name in datatype_names]
        datatypes = z3.CreateDatatypes(*args)
        self.types.update(
            {name:datatype for name,datatype in zip(datatype_names, datatypes)})


class DeclaredTypes(ThoriumVisitor):
    def visitProg(self, ctx:ThoriumParser.ProgContext):
        return lmap(self.visit, ctx.decl())

    def visitDecl(self, ctx:ThoriumParser.DeclContext):
        if ctx.enum(): return self.visit(ctx.enum())
        if ctx.struct(): return self.visit(ctx.struct())
        if ctx.reactor(): return self.visit(ctx.reactor())

    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        return ReactorType(ctx,
                           ctx.ID().getText(),
                           self.visitOrDefault(ctx.reactorParams(),[]),
                           self.visitOrDefault(ctx.reactorMembers(0),[]),
                           self.visitOrDefault(ctx.reactorMembers(1),[]))

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


def hasStreamType(types):
    for type in types:
        if isinstance(type,Stream):
            return True
    return False


class ReactorSubexpressionVisitor(ThoriumVisitor):
    def __init__(self,type_decls):
        self.type_decls = type_decls

    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        self.reactor = self.type_decls[ctx.ID().getText()]
        [self.visit(m) for m in ctx.reactorMembers()]
        #for members in ctx.reactorMembers():
        #    print(f'visiting members {members}')
        #    return lmap(self.visit, members.reactorMember())

    def visitReactorMember(self, ctx:ThoriumParser.ReactorMemberContext):
        self.expr = ctx.ID().getText()
        print(f'visitReactorMember set self.expr to {self.expr}')
        self.visit(ctx.expr())

    def visitNegative(self, ctx:ThoriumParser.NegativeContext):
        expr = self.expr
        self.expr = f'{expr}-1'
        type = self.visit(ctx.expr())
        self.reactor.addSubExpr(self.expr,type)
        return type

    def visitId(self, ctx:ThoriumParser.IdContext):
        return self.reactor.getType(ctx.ID().getText())

    def visitNumber(self, ctx:ThoriumParser.NumberContext):
        return 'int'

    def visitParen(self, ctx:ThoriumParser.ParenContext):
        return self.visit(ctx.expr())

    def visitSubExprs(self,ctx):
        expr = self.expr
        types = []
        for i,sub in enumerate(ctx.expr()):
            subexpr = f'{expr}-{i+1}'
            self.expr = subexpr
            type = self.visit(sub)
            types.append(type)
            self.reactor.addSubExpr(subexpr,type)
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

    def visitAnd(self, ctx:ThoriumParser.AndContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types): return Stream('bool')
        return Cell('bool')

    def visitOr(self, ctx:ThoriumParser.AndContext):
        types = self.visitSubExprs(ctx)
        if hasStreamType(types): return Stream('bool')
        return Cell('bool')

    def visitSnapshot(self, ctx:ThoriumParser.SnapshotContext):
        cellType,streamType = self.visitSubExprs(ctx)
        #TODO: typeCheck
        if isinstance(cellType,Cell):
            return Stream(cellType.type)
        return Stream(cellType)

    def visitAlternate(self, ctx:ThoriumParser.AlternateContext):
        typeA,typeB = self.visitSubExprs(ctx)
        #TODO: typeCheck (both should be the same kind of stream)
        return typeA

    def visitHold(self, ctx:ThoriumParser.HoldContext):
        cellType,streamType = self.visitSubExprs(ctx)
        #TODO: typeCheck (both should hold the same kind of value)
        if isinstance(cellType,Cell):
            return cellType
        return Cell(cellType)



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
        print(f'member {ctx.ID()} = {self.visit(ctx.expr())}')
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


class ReactorDefiner(ThoriumVisitor):
    def __init__(self, function:z3.Function, type_:object, type_decls:dict, type_context:TypeContext, first_state, final_state):
        ThoriumVisitor.__init__(self)
        self.function = function
        self.reactor_type = type_
        print(f'creating ReactorDefiner with type: {self.reactor_type} {type(self.reactor_type)}')
        self.type_decls = type_decls
        self.type_context = type_context
        self.first_state = first_state
        self.final_state = final_state

    def run(self):
        print(f'calling run on ReactorDefiner with type: {self.reactor_type} {type(self.reactor_type)}')
        self.visit(self.reactor_type.ctx)

    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        print(f'ReactorDefiner visiting {ctx.ID()}')

def main(argv):
    input_stream = antlr4.FileStream(argv[1])
    lexer = ThoriumLexer(input_stream)
    stream = antlr4.CommonTokenStream(lexer)
    parser = ThoriumParser(stream)
    tree = parser.prog();

    type_decl_visitor = DeclaredTypes()
    type_decls = type_decl_visitor.visitProg(tree)
    type_context = TypeContext()
    for decl in type_decls:
        type_context.addDatatype(decl)
    type_decls = {decl.name:decl for decl in type_decls}
    subexprs = ReactorSubexpressionVisitor(type_decls)
    subexprs.visitProg(tree)
    for decl in type_decls.values():
        print(repr(decl))
    type_context.finalizeDatatypes()
    visitor = PrintVisitor()
    visitor.visitProg(tree)
    Counter = type_context('counter')
    StreamTest = type_context(Stream('unit'))
    x = z3.Const('x',type_context('int'))
    #y = z3.Const('y',Counter)
    s = z3.Solver()
    #print(StreamTest.constructor(1))
    #print(StreamTest.nothing.constructor(0))
    #help(StreamTest)
    counter_main = z3.Function('counter-main',z3.IntSort(),Counter)
    print(f"type_decls['counter'] = {type_decls['counter']}")
    ReactorDefiner(counter_main, type_decls['counter'], type_decls, type_context, 0, 5).run()
    s.add(Counter.sum(counter_main(0)) == x)
    s.add(Counter.click(counter_main(1)) != StreamTest.nothing)
    s.add(x == 5)
    print(f'check returned {s.check()}')
    print(s.model())

if __name__ == '__main__':
    main(sys.argv)
