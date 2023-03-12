from thorium import ThoriumVisitor, ThoriumParser
from thorium.decls import Function
from thorium.reactivetypes import Cell, Stream, base_type


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
        if ctx.ID().getText() in ['active','inactive']:
            return Stream('bool')
        if ctx.ID().getText() == 'unit':
            return Stream('unit')

        f = self.decls[ctx.ID().getText()]
        if isinstance(f, Function):
            result_type = f.result_type
        else:
            result_type = f.name
            #TODO: handle reactors properly, the type should be Array[f.name]
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