from thorium import ThoriumVisitor, ThoriumParser
from thorium.decls import Function, ReactorType, StructType, TypedIdentifier
from thorium.reactivetypes import Cell, Stream


def lmap(f, iterable):
    return list(map(f, iterable))


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
