from thorium import ThoriumParser
from thorium import ThoriumVisitor
import z3
from thorium.reactor_definer import ReactorDefiner

class SnapshotTrigger(ReactorDefiner):
    def __init__(self, parent: ReactorDefiner):
        ThoriumVisitor.__init__(self)
        self.solver = parent.solver
        self.trace = parent.trace
        self.reactor_type = parent.reactor_type
        self.z3_reactor_type = parent.z3_reactor_type
        self.first_state = parent.first_state
        self.k0 = parent.first_state
        self.final_state = parent.final_state
        self.composite_types = parent.composite_types
        self.functions = parent.functions
        self.z3_types = parent.z3_types
        self.local_scope = {}
        self.const_def = parent.const_def
        self.debug_assert = parent.debug_assert

    def visitNot(self, ctx: ThoriumParser.NotContext):
        arg = self[self.expr_name(ctx.expr())]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.Assert(z3.If(arg.isNothing(k),
                              result[k] == True,
                              result.isNothing(k)))
        self.visitChildren(ctx)

    def visitAnd(self, ctx: ThoriumParser.AndContext):
        result, (arg0, arg1) = self.getRVs(ctx, ctx.expr())
        for k in self.all_states():
            self.Assert(z3.If(
                z3.Not(z3.Or(arg0.isNothing(k), arg1.isNothing(k))),
                result.setValue(k, True),
                result.isNothing(k)))
        self.visitChildren(ctx)

    def visitOr(self, ctx: ThoriumParser.AndContext):
        result, (arg0, arg1) = self.getRVs(ctx, ctx.expr())
        for k in self.streaming_states():
            self.Assert(z3.If(
                z3.Not(z3.And(arg0.isNothing(k), arg1.isNothing(k))),
                result.setValue(k, True),
                result.isNothing(k)))
        self.visitChildren(ctx)
