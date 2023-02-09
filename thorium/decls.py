from thorium import ThoriumVisitor, ThoriumParser
from thorium.operators import Operators
import z3
from typing import List

class TypedIdentifier:
    def __init__(self, name, type_):
        self.name = name
        self.type = type_

    def __repr__(self):
        return f'{self.name} : {self.type}'


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
        property = self.visit(ctx.expr())
        # print(f'function property {property}')
        self.solver.add(property)

    def visitMemberAccess(self, ctx: ThoriumParser.MemberAccessContext):
        print('*************************************** not implemented')
        pass

    def visitId(self, ctx: ThoriumParser.IdContext):
        return self.symbols[ctx.ID().getText()]

    def visitNumber(self, ctx: ThoriumParser.NumberContext):
        return int(ctx.NUMBER().getText())

    def visitBool(self, ctx: ThoriumParser.BoolContext):
        return bool(ctx.TRUE())

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

