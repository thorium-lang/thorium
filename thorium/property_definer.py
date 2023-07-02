from thorium import ThoriumParser
from thorium import ThoriumVisitor
import z3

from thorium.reactivetypes import ReactiveValue
from thorium.reactor_definer import ReactorDefiner

class PropertyDefiner(ReactorDefiner):
    def __init__(self, parent: ReactorDefiner):
        ThoriumVisitor.__init__(self)
        self.solver = parent.solver
        self.trace = parent.trace
        self.reactor_type = parent.reactor_type
        self.z3_reactor_type = parent.z3_reactor_type
        self.first_state = parent.first_state
        self.k0 = parent.first_state
        self.final_state = parent.final_state
        self.kK = parent.final_state
        self.composite_types = parent.composite_types
        self.functions = parent.functions
        self.z3_types = parent.z3_types

    def visitLtlNegation(self, ctx: ThoriumParser.LtlNegationContext):
        result, arg = self.getRVs(ctx, ctx.ltlProperty())
        for k in self.all_states():
            self.Assert(result[k]==z3.Not(arg.isTrue(k)))
        self.visitChildren(ctx)

    def visitNot(self, ctx: ThoriumParser.NotContext):
        result, arg = self.getRVs(ctx, ctx.expr())
        for k in self.all_states():
            self.Assert(result[k]==z3.Not(arg.isTrue(k)))
        self.visitChildren(ctx)

    def visitLtlAnd(self, ctx: ThoriumParser.LtlAndContext):
        result, (arg0, arg1) = self.getRVs(ctx, ctx.ltlProperty())
        for k in self.all_states():
            self.Assert(result(k) == z3.And(arg0.isTrue(k), arg1.isTrue(k)))
        self.visitChildren(ctx)

    def visitAnd(self, ctx: ThoriumParser.AndContext):
        result, (arg0,arg1) = self.getRVs(ctx, ctx.expr())
        for k in self.all_states():
            self.Assert(result(k) == z3.And(arg0.isTrue(k), arg1.isTrue(k)))
        self.visitChildren(ctx)

    def visitLtlOr(self, ctx: ThoriumParser.AndContext):
        result, (arg0, arg1) = self.getRVs(ctx, ctx.ltlProperty())
        for k in self.all_states():
            self.Assert(result(k) == z3.Or(arg0.isTrue(k), arg1.isTrue(k)))
        self.visitChildren(ctx)

    def visitOr(self, ctx: ThoriumParser.AndContext):
        result, (arg0,arg1) = self.getRVs(ctx, ctx.expr())
        for k in self.all_states():
            self.Assert(result(k) == z3.Or(arg0.isTrue(k), arg1.isTrue(k)))
        self.visitChildren(ctx)

    def next(self, result: ReactiveValue, arg: ReactiveValue):
        for k in self.all_states()[:-1]:
            self.Assert(result(k) == arg.isTrue(k+1))
        self.Assert(result.isTrue(self.kK))

    def visitLtlNext(self, ctx:ThoriumParser.LtlNextContext):
        result, arg = self.getRVs(ctx, ctx.ltlProperty())
        self.next(result, arg)
        self.visitChildren(ctx)

    def globally(self, result: ReactiveValue, arg: ReactiveValue):
        for k in self.all_states():
            self.Assert(result(k) == z3.And(arg.isTrue(k), result(k+1)))
        self.Assert(result.isTrue(self.kK+1))  # optimistic semantics

    def visitLtlGlobally(self, ctx: ThoriumParser.LtlGloballyContext):
        result, arg = self.getRVs(ctx, ctx.ltlProperty())
        self.globally(result, arg)
        self.visitChildren(ctx)

    def eventually(self, result: ReactiveValue, arg: ReactiveValue):
        for k in self.all_states():
            self.Assert(result(k) == z3.Or(arg.isTrue(k), result(k+1)))
        self.Assert(z3.Not(result.isTrue(self.kK+1)))  # pessimistic semantics

    def visitLtlEventually(self, ctx: ThoriumParser.LtlEventuallyContext):
        result, arg = self.getRVs(ctx, ctx.ltlProperty())
        self.eventually(result, arg)
        self.visitChildren(ctx)

    def until(self, U: ReactiveValue, p: ReactiveValue, q: ReactiveValue):
        for k in self.all_states():
            self.Assert(U(k) == z3.Or(q.isTrue(k),
                                      z3.And(p.isTrue(k),
                                             U(k+1))))
        self.Assert(z3.Not(U(self.kK+1)))

    def visitLtlUntil(self, ctx: ThoriumParser.LtlUntilContext):
        result, (p, q) = self.getRVs(ctx, ctx.ltlProperty())
        self.until(result, p, q)
        self.visitChildren(ctx)

    def since(self, S: ReactiveValue, p: ReactiveValue, q: ReactiveValue):
        self.Assert(z3.Not(S(self.k0-1)))
        for k in self.all_states():
            self.Assert(S(k) == z3.Or(q.isTrue(k),
                                      z3.And(p.isTrue(k),
                                             S(k-1))))

    def visitLtlSince(self, ctx: ThoriumParser.LtlSinceContext):
        result, (p, q) = self.getRVs(ctx, ctx.ltlProperty())
        self.since(result, p, q)
        self.visitChildren(ctx)

    def visitLtlParen(self, ctx: ThoriumParser.LtlParenContext):
        self.visitChildren(ctx)

    def implication(self, result: ReactiveValue, p: ReactiveValue, q: ReactiveValue):
        for k in self.all_states():
            self.Assert(result[k]==z3.Or(q.isTrue(k), z3.Not(p.isTrue(k))))
            #TODO: this should have worked, but the typechecking needs improvement
            #      for stream arguments.
            #self.Assert(result(k) == z3.Or(q.isTrue(k), z3.Not(p.isTrue(k))))

    def visitLtlImplication(self, ctx: ThoriumParser.LtlImplicationContext):
        result, (p, q) = self.getRVs(ctx, ctx.ltlProperty())
        self.implication(result, p, q)
        self.visitChildren(ctx)

    def visitImplication(self, ctx: ThoriumParser.ImplicationContext):
        result, (p, q) = self.getRVs(ctx, ctx.expr())
        self.implication(result, p, q)
        self.visitChildren(ctx)
