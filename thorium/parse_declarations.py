from thorium import ThoriumVisitor, ThoriumParser
from thorium.decls import Function, ReactorType, StructType, EnumType, \
                          TypedIdentifier
from thorium.reactivetypes import Const, Cell, Stream
from collections.abc import Iterable


def lmap(f, iterable):
    return list(map(f, iterable))


def flatten(iterable):
    for item in iterable:
        if isinstance(item, Iterable):
            for x in flatten(item):
                yield x
        else:
            yield item


def lflatten(iterable):
    return list(flatten(iterable))


class _namespace:
    def __init__(self):
        self.namespaces = []

    def push(self, name):
        self.namespaces.append(name)

    def pop(self):
        name = self.namespaces[-1]
        self.namespaces = self.namespaces[:-1]

    def __call__(self):
        return '::'.join(self.namespaces)


class _namespace_scope:
    def __init__(self, namespace, name):
        self.namespace = namespace
        self.name = name

    def __enter__(self):
        self.namespace.push(self.name)
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        self.namespace.pop()


class ParseDeclarations(ThoriumVisitor):
    def __init__(self,debug=False):
        self.debug = debug
        super().__init__()
        self.__namespace = _namespace()

    def __scope(self,name):
        return _namespace_scope(self.__namespace, name)

    def visitProg(self, ctx: ThoriumParser.ProgContext):
        return lflatten(map(self.visit, ctx.decl()))

    def visitDecl(self, ctx: ThoriumParser.DeclContext):
        return self.visit(ctx.children[0])  # there can be only one child

    def visitFunction(self, ctx: ThoriumParser.FunctionContext):
        return Function(ctx)

    def visitOrDefault(self, node, default):
        if node:
            return self.visit(node)
        return default

    def visitReactor(self, ctx: ThoriumParser.ReactorContext):
        return ReactorType(ctx,
                           ctx.ID().getText(),
                           self.visitOrDefault(ctx.reactorParams(), []),
                           self.visitOrDefault(ctx.reactorMembers(0), []),
                           self.visitOrDefault(ctx.reactorMembers(1), []),
                           self.visitOrDefault(ctx.reactorProperties(), []))

    def visitDatatype(self, ctx:ThoriumParser.DatatypeContext):
        with self.__scope(ctx.ID().getText()):
            datatype = self.visit(ctx.struct() if ctx.struct() else ctx.enum())
            return datatype.finalize_datatypes()

    def visitStruct(self, ctx: ThoriumParser.StructContext):
        return StructType(ctx, self.__namespace(),
                               self.visit(ctx.structMembers()))

    def visitEnum(self, ctx:ThoriumParser.EnumContext):
        return EnumType(ctx, self.__namespace(),
                             self.visit(ctx.enumMembers()))

    def visitReactiveType(self, ctx: ThoriumParser.ReactiveTypeContext):
        if ctx.CONST():
            return Const(self.visit(ctx.type_()))
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

    def visitFirst(self, *contexts):
        for context in contexts:
            if context:
                return self.visit(context)

    def visitStructMember(self, ctx: ThoriumParser.StructMemberContext):
        with self.__scope(ctx.ID().getText()):
            return TypedIdentifier(ctx.ID().getText(),
                                   self.visitFirst(ctx.struct(),
                                                   ctx.enum(),
                                                   ctx.type_()))

    def visitEnumMembers(self, ctx:ThoriumParser.EnumMembersContext):
        return lmap(self.visit, ctx.enumMember())

    def visitEnumMember(self, ctx:ThoriumParser.EnumMemberContext):
        with self.__scope(ctx.ID().getText()):
            return TypedIdentifier(ctx.ID().getText(),
                                   self.visitFirst(ctx.struct(),
                                                   ctx.enum(),
                                                   ctx.type_()))

    def visitReactorMembers(self, ctx: ThoriumParser.ReactorMembersContext):
        return lmap(self.visit, ctx.reactorMember())

    def visitReactorMember(self, ctx: ThoriumParser.ReactorMemberContext):
        return TypedIdentifier(ctx.ID().getText(), self.visit(ctx.reactiveType()))

    def visitReactorProperties(self, ctx: ThoriumParser.ReactorPropertiesContext):
        return lmap(self.visit, ctx.reactorProperty())

    def visitReactorProperty(self, ctx: ThoriumParser.ReactorPropertyContext):
        return TypedIdentifier(ctx.ID().getText(), Cell('bool'))
