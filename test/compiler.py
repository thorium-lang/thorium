#!/usr/bin/env python3
import operator
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
        if name in self.subexprs_dict: return self.subexprs_dict[name]
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
            datatype.declareZ3Constructor(self)
        datatype_names = [str(dt) for dt in self.datatypes]
        args = [self(name) for name in datatype_names]
        datatypes = z3.CreateDatatypes(*args)
        self.types.update(
            {name:datatype for name,datatype in zip(datatype_names, datatypes)})


class CompositeTypes(ThoriumVisitor):
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


class SubExprTypeCheck(ThoriumVisitor):
    def __init__(self,type_decls):
        self.type_decls = type_decls

    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        self.reactor = self.type_decls[ctx.ID().getText()]
        [self.visit(m) for m in ctx.reactorMembers()]

    def visitReactorMember(self, ctx:ThoriumParser.ReactorMemberContext):
        ctx.expr().membername = ctx.ID().getText()
        self.visit(ctx.expr())

    def visitNegative(self, ctx:ThoriumParser.NegativeContext):
        ctx.expr().membername = f'{ctx.membername}-1'
        type = self.visit(ctx.expr())
        self.reactor.addSubExpr(ctx.expr().membername,type)
        return type

    def visitId(self, ctx:ThoriumParser.IdContext):
        id = ctx.ID().getText()
        return self.reactor.getType(id)

    def visitNumber(self, ctx:ThoriumParser.NumberContext):
        return 'int'

    def visitParen(self, ctx:ThoriumParser.ParenContext):
        ctx.expr().membername = ctx.membername
        return self.visit(ctx.expr())

    def visitSubExprs(self,ctx):
        types = []
        for i,sub in enumerate(ctx.expr()):
            sub.membername = f'{ctx.membername}-{i+1}'
            type = self.visit(sub)
            types.append(type)
            self.reactor.addSubExpr(sub.membername,type)
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


class ReactorDefiner(ThoriumVisitor):
    #ReactorDefiner(counter_main, composite_types['counter'], composite_types, z3_types, 0, 5).run()
    def __init__(self, composite_types:dict, z3_types:Z3Types):
        ThoriumVisitor.__init__(self)
        self.solver = None
        self.function = None
        self.reactor_type = None
        self.first_state = None
        self.final_state = None
        self.composite_types = composite_types
        self.z3_types = z3_types

    def __call__(self, name: str, typename: str, first_state: int, final_state: int, solver: z3.Solver):
        self.reactor_type = self.composite_types[typename]
        self.z3_reactor_type = self.z3_types(typename)
        self.function = z3.Function(name, z3.IntSort(), self.z3_reactor_type)
        self.first_state = first_state
        self.final_state = final_state
        self.solver = solver
        print(f'calling run on ReactorDefiner with type: {self.reactor_type} {type(self.reactor_type)}')
        self.visit(self.reactor_type.ctx)
        return self.function

    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        print(f'ReactorDefiner visiting {ctx.ID()}')
        self.visitChildren(ctx)

    def visitNegative(self, ctx:ThoriumParser.NegativeContext):
        print(f'Reactor {self.reactor_type}, {ctx.membername} = - {ctx.expr().membername}')
        accessor = self.z3_reactor_type.__getattribute__(ctx.membername)
        expr_accessor = self.z3_reactor_type.__getattribute__(ctx.expr().membername)
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(accessor(self.function(k)) == - expr_accessor(self.function(k)))
        self.visitChildren(ctx)

    def visitId(self, ctx:ThoriumParser.IdContext):
        accessor = self.z3_reactor_type.__getattribute__(ctx.membername)
        id_accessor = self.z3_reactor_type.__getattribute__(ctx.ID().getText())
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.ID()}')
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(accessor(self.function(k)) == id_accessor(self.function(k)))
        self.visitChildren(ctx)

    def visitNumber(self, ctx:ThoriumParser.NumberContext):
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.NUMBER()}')
        value = int(ctx.NUMBER().getText())
        accessor = self.z3_reactor_type.__getattribute__(ctx.membername)
        for k in range(self.first_state, self.final_state+1):
            self.solver.add(accessor(self.function(k)) == value)
        self.visitChildren(ctx)

    def visitMult(self, ctx:ThoriumParser.MultContext):
        OP = '*'
        if ctx.DIV(): OP = '/'
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.expr(0).membername} {OP} {ctx.expr(1).membername}')
        self.visitChildren(ctx)

    def visitAdd(self, ctx:ThoriumParser.AddContext):
        accessor = self.z3_reactor_type.__getattribute__(ctx.membername)
        arg0_accessor = self.z3_reactor_type.__getattribute__(ctx.expr(0).membername)
        arg1_accessor = self.z3_reactor_type.__getattribute__(ctx.expr(1).membername)

        arg0_type = self.reactor_type.getType(ctx.expr(0).membername)
        arg1_type = self.reactor_type.getType(ctx.expr(1).membername)

        z3_expr_type = self.z3_types(self.reactor_type.getType(ctx.membername))
        z3_arg0_type = self.z3_types(self.reactor_type.getType(ctx.expr(0).membername))
        z3_arg1_type = self.z3_types(self.reactor_type.getType(ctx.expr(1).membername))
        f = self.function
        OP = operator.add
        if ctx.MINUS(): OP = operator.sub
        if not (isinstance(arg0_type, Stream) or isinstance(arg1_type, Stream)):
            for k in range(self.first_state, self.final_state+1):
                self.solver.add(accessor(f(k)) == OP(arg0_accessor(f(k)), arg1_accessor(f(k))))
        elif isinstance(arg0_type, Stream) and isinstance(arg1_type, Stream):
            self.solver.add(accessor(f(self.first_state)) == z3_expr_type.nothing)
            for k in range(self.first_state+1, self.final_state+1):
                self.solver.add(accessor(f(k)) == z3.If(arg0_accessor(f(k)) == z3_arg0_type.nothing or
                                                        arg1_accessor(f(k)) == z3_arg1_type.nothing,
                                                        z3_expr_type.nothing,
                                                        z3_expr_type.event(OP( z3_arg0_type.value(arg0_accessor(f(k))),
                                                                               z3_arg1_type.value(arg1_accessor(f(k)))))))
        elif isinstance(arg1_type, Stream):
            self.solver.add(accessor(f(self.first_state)) == z3_expr_type.nothing)
            print(accessor,type(accessor))
            print(arg0_accessor)
            print(arg1_accessor)
            print(z3_expr_type)
            print(z3_arg0_type)
            print(z3_arg1_type)
            for k in range(self.first_state+1, self.final_state+1):
                self.solver.add(accessor(f(k)) == z3.If(arg1_accessor(f(k)) == z3_arg1_type.nothing,
                                                        z3_expr_type.nothing,
                                                        #z3_expr_type.event(z3_arg1_type.value(arg1_accessor(f(k))))))
                                                        z3_expr_type.event(OP( arg0_accessor(f(k-1)),
                                                                               z3_arg1_type.value(arg1_accessor(f(k)))))))
        elif isinstance(arg0_type, Stream):
            self.solver.add(accessor(f(self.first_state)) == z3_expr_type.nothing)
            for k in range(self.first_state+1, self.final_state+1):
                self.solver.add(accessor(f(k)) == z3.If( arg0_accessor(f(k)) == z3_arg0_type.nothing,
                                                         z3_expr_type.nothing,
                                                         z3_expr_type.event(OP( z3_arg0_type.value(arg0_accessor(f(k))),
                                                                                arg1_accessor(f(k-1))))))

        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.expr(0).membername} {OP} {ctx.expr(1).membername}')
        self.visitChildren(ctx)

    def visitCompare(self, ctx:ThoriumParser.CompareContext):
        OP = '<'
        if ctx.LE(): '<='
        if ctx.GT(): '>'
        if ctx.GE(): '>='
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.expr(0).membername} {OP} {ctx.expr(1).membername}')
        self.visitChildren(ctx)

    def visitEquals(self, ctx:ThoriumParser.EqualsContext):
        OP = '=='
        if ctx.NEQ(): '!='
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.expr(0).membername} {OP} {ctx.expr(1).membername}')
        self.visitChildren(ctx)

    def visitAnd(self, ctx:ThoriumParser.AndContext):
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.expr(0).membername} and {ctx.expr(1).membername}')
        self.visitChildren(ctx)

    def visitOr(self, ctx:ThoriumParser.AndContext):
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.expr(0).membername} or {ctx.expr(1).membername}')
        self.visitChildren(ctx)

    def visitSnapshot(self, ctx:ThoriumParser.SnapshotContext):
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.expr(0).membername} @ {ctx.expr(1).membername}')
        accessor = self.z3_reactor_type.__getattribute__(ctx.membername)
        cell_accessor = self.z3_reactor_type.__getattribute__(ctx.expr(0).membername)
        stream_accessor = self.z3_reactor_type.__getattribute__(ctx.expr(1).membername)
        snap_type = self.z3_types(self.reactor_type.getType(ctx.membername))
        stream_type = self.z3_types(self.reactor_type.getType(ctx.expr(1).membername))
        self.solver.add(accessor(self.function(self.first_state)) == snap_type.nothing)
        for k in range(self.first_state+1, self.final_state+1):
            self.solver.add(accessor(self.function(k)) == z3.If(stream_accessor(self.function(k))==stream_type.nothing,
                                                                snap_type.nothing,
                                                                snap_type.event(cell_accessor(self.function(k-1)))))
        self.visitChildren(ctx)

    def visitAlternate(self, ctx:ThoriumParser.AlternateContext):
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.expr(0).membername} | {ctx.expr(1).membername}')
        self.visitChildren(ctx)

    def visitHold(self, ctx:ThoriumParser.HoldContext):
        print(f'Reactor {self.reactor_type}, {ctx.membername} = {ctx.expr(0).membername} .. {ctx.expr(1).membername}')
        accessor = self.z3_reactor_type.__getattribute__(ctx.membername)
        cell_accessor = self.z3_reactor_type.__getattribute__(ctx.expr(0).membername)
        stream_accessor = self.z3_reactor_type.__getattribute__(ctx.expr(1).membername)
        stream_type = self.z3_types(self.reactor_type.getType(ctx.expr(1).membername))
        self.solver.add(accessor(self.function(0)) == cell_accessor(self.function(0)))
        for k in range(self.first_state+1, self.final_state+1):
            self.solver.add(accessor(self.function(k)) == z3.If(stream_accessor(self.function(k))==stream_type.nothing,
                                                                accessor(self.function(k-1)),
                                                                stream_type.value(stream_accessor(self.function(k)))))
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


def main(argv):
    input_stream = antlr4.FileStream(argv[1])
    lexer = ThoriumLexer(input_stream)
    stream = antlr4.CommonTokenStream(lexer)
    parser = ThoriumParser(stream)
    tree = parser.prog();

    composite_types = CompositeTypes().visitProg(tree)
    z3_types = Z3Types()
    for composite_type in composite_types:
        z3_types.addDatatype(composite_type)
    composite_types = {t.name:t for t in composite_types}
    SubExprTypeCheck(composite_types).visitProg(tree)
    z3_types.finalizeDatatypes()

    for t in composite_types.values():
        print(repr(t))

    PrintVisitor().visitProg(tree)

    reactor_definer = ReactorDefiner(composite_types, z3_types)

    solver = z3.Solver()
    counter_main = reactor_definer('counter-main', 'counter', 0, 5, solver)

    Counter = z3_types('counter')
    solver.add(Counter.sum(counter_main(5))==4)

    print(f'check returned {solver.check()}')
    print(solver.model())

    solution = solver.model()[counter_main]
    #help(solution)
    f = {a.as_long():b for a,b in solution.as_list()[:-1]}
    for k in range(6):
        if k in f:
            print(f[k])
        else:
            print(solution.else_value())
    #help(list(f.keys())[0])
    #print(solver.model()[counter_main].entry(0))

    """
    StreamTest = z3_types(Stream('unit'))
    x = z3.Const('x',z3_types('int'))
    #y = z3.Const('y',Counter)
    #print(StreamTest.constructor(1))
    #print(StreamTest.nothing.constructor(0))
    #help(StreamTest)
    print(f"type_decls['counter'] = {type_decls['counter']}")
    s.add(Counter.sum(counter_main(0)) == x)
    s.add(Counter.click(counter_main(1)) != StreamTest.nothing)
    s.add(x == 5)
    print(f'check returned {s.check()}')
    print(s.model())
    """

if __name__ == '__main__':
    main(sys.argv)
