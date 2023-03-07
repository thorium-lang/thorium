from thorium import ThoriumVisitor, ThoriumParser
from thorium.z3types import Z3Types
from thorium.operators import Operators
from typing import List
import z3
from thorium.reactivetypes import ReactiveValue
from thorium.reactivetypes import base_type
from thorium.decls import StructType,ReactorType


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

    def expr_name(self, ctx):
        return self.reactor_type.expr_name(ctx)

    def all_states(self):
        return range(self.first_state, self.final_state+1)

    def streaming_states(self):
        return range(self.first_state+1, self.final_state+1)

    def Assert(self, statement):
        # if 'good' in str(statement):
        #    print(statement)
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
        self.trace = z3.Array(name,z3.IntSort(), self.z3_reactor_type)
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
        if composite.isStream():
            accessor = self.z3_types(base_type(composite.thorium_type)).__getattribute__(ctx.ID().getText())
        else:
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
            self.Assert(result(k) == id(k))
        self.visitChildren(ctx)

    def visitNumber(self, ctx: ThoriumParser.NumberContext):
        value = int(ctx.NUMBER().getText())
        accessor = self.z3_reactor_type.__getattribute__(self.expr_name(ctx))
        for k in range(self.first_state, self.final_state+1):
            self.Assert(accessor(self.trace[k]) == value)
        self.visitChildren(ctx)

    def visitUnit(self, ctx:ThoriumParser.UnitContext):
        (result,) = self.getRVs(ctx)
        unit = self.z3_types('unit')
        for k in self.all_states():
            self.Assert(result(k)==unit.unit)


    def visitBool(self, ctx: ThoriumParser.BoolContext):
        (result,) = self.getRVs(ctx)
        for k in self.all_states():
            self.Assert(result(k) == bool(ctx.TRUE()))
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
            if isinstance(f, ReactorType):
                return f

    def unit(self,args,result):
        stream_args = [arg for arg in args if arg.isStream()]
        if stream_args:
            self.Assert(result.isNothing(self.first_state))
            for k in self.streaming_states():
                missing_args = z3.Or(*[arg.isNothing(k) for arg in stream_args])
                self.Assert(z3.If(missing_args,
                                  result.isNothing(k),
                                  result.setValue(k, self.z3_types('unit').unit)))
        else:
            for k in self.all_states():
                self.Assert(result.setValue(k, self.z3_types('unit').unit))

    def visitApply(self, ctx: ThoriumParser.ApplyContext):
        args = [self[self.expr_name(expr)] for expr in ctx.expr()]
        result = self[self.expr_name(ctx)]
        if ctx.ID().getText()=='unit':
            from thorium.snapshot_trigger import SnapshotTrigger
            SnapshotTrigger(self).visitChildren(ctx)
            self.unit(args,result)
        else:
            callable = self[ctx.ID().getText()]
            if isinstance(callable, ReactorType):
                #do composition
                raise Exception("Reactor composition not yet supported.")
            else:
                self.apply(callable, args, result)
                self.visitChildren(ctx)

    def visitLtlNegation(self, ctx: ThoriumParser.LtlNegationContext):
        arg = self[self.expr_name(ctx.ltlProperty())]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.Assert(result.setValue(k, z3.Not(arg.isTrue(k))))
        self.visitChildren(ctx)

    def next(self, result, arg):
        for k in self.all_states()[:-1]:
            self.Assert(result(k) == arg.isTrue(k+1))
        self.Assert(result(self.final_state) == True)  # optimistic semantics

    def visitLtlNext(self, ctx:ThoriumParser.LtlNextContext):
        result, arg = self.getRVs(ctx, ctx.ltlProperty())
        self.next(result, arg)
        self.visitChildren(ctx)

    def globally(self, result, arg):
        for k in self.all_states():
            self.Assert(result(k) == z3.And(arg.isTrue(k), result(k+1)))
        self.Assert(result(self.final_state+1) == True)  # optimistic semantics

    def visitLtlGlobally(self, ctx: ThoriumParser.LtlGloballyContext):
        result, arg = self.getRVs(ctx, ctx.ltlProperty())
        self.globally(result, arg)
        self.visitChildren(ctx)

    def visitLtlEventually(self, ctx: ThoriumParser.LtlEventuallyContext):
        arg = self[self.expr_name(ctx.ltlProperty())]
        result = self[self.expr_name(ctx)]
        for k in self.all_states():
            self.Assert(result(k) == z3.Or(arg.isTrue(k), result.getValue(k+1)))
        self.Assert(result(self.final_state) == False)  # optimistic semantics
        self.visitChildren(ctx)

    def visitLtlUntil(self, ctx: ThoriumParser.LtlUntilContext):
        arg0 = self[self.expr_name(ctx.ltlProperty(0))]
        arg1 = self[self.expr_name(ctx.ltlProperty(1))]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.Assert(result.setValue(k, z3.Or(arg1.isTrue(k), z3.And(arg0.isTrue(k), result.getValue(k+1)))))
        self.Assert(result.setValue(self.final_state+1, True))  # optimistic semantics
        self.visitChildren(ctx)

    def since(self, p, q, S):
        self.Assert(z3.Not(S(self.k0-1)))
        for k in self.all_states():
            self.Assert(S(k) == z3.Or(q.isTrue(k),
                                      z3.And(p.isTrue(k),
                                             S(k-1))))

    def visitLtlSince(self, ctx: ThoriumParser.LtlSinceContext):
        result, (p, q) = self.getRVs(ctx, ctx.ltlProperty())
        self.since(p, q, result)
        self.visitChildren(ctx)

    def visitLtlParen(self, ctx: ThoriumParser.LtlParenContext):
        self.visitChildren(ctx)

    def visitLtlAnd(self, ctx: ThoriumParser.LtlAndContext):
        arg0 = self[self.expr_name(ctx.ltlProperty(0))]
        arg1 = self[self.expr_name(ctx.ltlProperty(1))]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.Assert(z3.If(z3.Or(arg0.isNothing(k), arg1.isNothing(k)),
                              result.setValue(k, False),
                              result.setValue(k, z3.And(arg0.getValue(k), arg1.getValue(k)))))
        self.visitChildren(ctx)

    def visitLtlImplication(self, ctx: ThoriumParser.LtlImplicationContext):
        arg0 = self[self.expr_name(ctx.ltlProperty(0))]
        arg1 = self[self.expr_name(ctx.ltlProperty(1))]
        result = self[self.expr_name(ctx)]
        for k in range(self.first_state, self.final_state+1):
            self.Assert(z3.If(arg0.isNothing(k),
                              result.setValue(k, True),
                              result.setValue(k, z3.Implies(arg0.getValue(k), arg1.getValue(k)))))
        self.visitChildren(ctx)

    def unaryOp(self, ctx):
        f = Operators.unary[ctx.op.text]
        arg0 = self[self.expr_name(ctx.expr())]
        result = self[self.expr_name(ctx)]
        self.apply(f, [arg0], result)

    def binOp(self, ctx):
        f = Operators.binary[ctx.op.text]
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
        self.Assert(result.isNothing(self.first_state))
        for k in range(self.first_state+1, self.final_state+1):
            self.Assert(z3.If(expr.getValue(k) != expr.getValue(k-1),
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
        self.unaryOp(ctx)
        self.visitChildren(ctx)

    def visitAnd(self, ctx: ThoriumParser.AndContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitImplication(self, ctx: ThoriumParser.ImplicationContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def visitOr(self, ctx: ThoriumParser.AndContext):
        self.binOp(ctx)
        self.visitChildren(ctx)

    def snapshot(self, result, cell, stream):
        self.Assert(result.isNothing(self.k0))
        for k in self.streaming_states():
            self.Assert(z3.If(stream.isNothing(k),
                              result.isNothing(k),
                              result.setValue(k, cell(k-1))))

    def visitSnapshot(self, ctx: ThoriumParser.SnapshotContext):
        result, (cell, stream) = self.getRVs(ctx, ctx.expr())
        self.snapshot(result, cell, stream)

        self.visit(ctx.expr(0))
        from thorium.snapshot_trigger import SnapshotTrigger
        SnapshotTrigger(self).visit(ctx.expr(1))

    def merge(self, result, s1, s2):
        self.Assert(result.isNothing(self.k0))
        for k in self.streaming_states():
            self.Assert(result(k) == z3.If(s1.isNothing(k),
                                           s2(k),
                                           s1(k)))

    def visitMerge(self, ctx: ThoriumParser.MergeContext):
        result, (s1, s2) = self.getRVs(ctx, ctx.expr())
        self.merge(result, s1, s2)
        self.visitChildren(ctx)

    def filter(self, result, value, condition):
        self.Assert(result.isNothing(self.k0))
        for k in self.streaming_states():
            self.Assert(z3.If(z3.Or(condition.isNothing(k),value.isNothing(k)),
                              result.isNothing(k),
                              z3.If(condition.getValue(k, True),
                                    result.setValue(k, value.getValue(k)),
                                    result.isNothing(k))))

    def visitFilter(self, ctx: ThoriumParser.FilterContext):
        result, (value, condition) = self.getRVs(ctx, ctx.expr())
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
        result, (init, update) = self.getRVs(ctx, ctx.expr())
        self.hold(result, init, update)
        self.visitChildren(ctx)
