from thorium import ThoriumVisitor, ThoriumParser
from thorium.z3types import Z3Types
from thorium.operators import Operators
from typing import List
import z3
from thorium.reactivetypes import ReactiveValue
from thorium.reactivetypes import base_type
from thorium.decls import StructType, ReactorType

TRACES = {}


class TraceHeap:
    def __init__(self, typename, z3_reactor_type):
        self.N = 0
        self.typename = typename
        self.traces = z3.Array(f'{typename}-heap',z3.IntSort(), z3.ArraySort(z3.IntSort(), z3_reactor_type))

    def allocate_trace(self):
        n = self.N
        self.N += 1
        return n,self.traces[n]

    def __getitem__(self, n):
        return self.traces[n]

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
        self.local_scope = {}
        self.traces = {}

    def expr_name(self, ctx):
        return self.reactor_type.expr_name(ctx)

    def all_states(self):
        return range(self.first_state-1, self.final_state+1)

    def streaming_states(self):
        return range(self.first_state, self.final_state+1)

    def Assert(self, statement, debug=False):
        if debug:
            print(statement)
        return self.solver.add(statement)

    def apply(self, f: callable,
              args: List[ReactiveValue],
              result: ReactiveValue,
              debug: bool=False):
        stream_args = [arg for arg in args if arg.isStream()]
        if stream_args:
            for k in self.all_states():
                active = z3.And(*[arg.isActive(k) for arg in stream_args])
                result.condSet(k, active, f(*[arg[k] for arg in args]))
        else:
            for k in self.all_states():
                result.setValue(k, f(*[arg[k] for arg in args]))

    def get_trace(self, index):
        global TRACES
        heap = TRACES[self.typename]
        return heap[index]

    def create_trace(self):
        global TRACES
        if self.typename not in TRACES:
            TRACES[self.typename] = TraceHeap(self.typename, self.z3_reactor_type)
        return TRACES[self.typename].allocate_trace()

    def __call__(self, name: str, typename: str, first_state: int, final_state: int, solver: z3.Solver):
        self.typename = typename
        self.reactor_type = self.composite_types[typename]
        self.z3_reactor_type = self.z3_types(typename)
        #self.trace = z3.Array(name,z3.IntSort(), self.z3_reactor_type)
        self.trace_ID, self.trace = self.create_trace()
        self.first_state = first_state
        self.k0 = first_state
        self.final_state = final_state
        self.kK = final_state
        self.solver = solver
        self.visit(self.reactor_type.ctx)
        return self.trace

    def visitReactorProperty(self, ctx:ThoriumParser.ReactorPropertyContext):
        from thorium.property_definer import PropertyDefiner
        PropertyDefiner(self).visitChildren(ctx)

    def visitReactor(self, ctx: ThoriumParser.ReactorContext):
        self.visitChildren(ctx)

    def getMemberType(self, composite, member_name):
        return self.composite_types\
            [base_type(composite.thorium_type)]\
                .getPublicMemberType(member_name)

    def getMemberAccessor(self, composite, member_name):
        composite_type = base_type(composite.thorium_type)
        composite_z3_type = self.z3_types(composite_type)
        if composite.isStream():
            return composite_z3_type.__getattribute__(member_name)
        if composite.isOptional():
            return composite_z3_type.__getattribute__(member_name)
        return composite_z3_type.__getattribute__(member_name)
        #return composite.z3_type.__getattribute__(member_name)

    def visitMatchCase(self, ctx:ThoriumParser.MatchCaseContext):
        result,value = self.getRVs(ctx, ctx.expr())
        instance = self.expr_for_match

        spec = ctx.ID().getText()
        spec_parts = spec.split('::')
        base = '::'.join(spec_parts[:-1])
        case = spec_parts[-1]
        case_checker = self.z3_types(base).__getattribute__(f'is_{spec}')
        argument_accessors = self.composite_types[base].constructorAccessors(case)
        base_z3_type = self.z3_types(base)
        if ctx.matchArgs():
            for arg,accessor in zip(ctx.matchArgs().ID(),argument_accessors):
                arg_member = f'{self.expr_name(ctx)}-{arg}'
                accessor = base_z3_type.__getattribute__(f'{spec}::{accessor}')
                self.local_scope[arg.getText()] = f'{self.expr_name(ctx)}-{arg}'
                arg_member = self[arg_member]
                for k in self.all_states():
                    arg_member[k]=accessor(instance[k])

        for k in self.streaming_states():
            print(self.reactor_type.getType(self.reactor_type.expr_name(ctx)))
            print(result(k))
            print(self.reactor_type.getType(self.reactor_type.expr_name(ctx.expr())))
            print(value(k))
            self.Assert(z3.If(
                z3.And(instance.isActive(k),
                       case_checker(instance[k])),
                result(k) == result.just(value[k]),
                result(k) == result.nothing), debug=False)
        self.visitChildren(ctx)
        self.local_scope = {}

    def visitMatchCases(self, ctx:ThoriumParser.MatchCasesContext):
        result,cases = self.getRVs(ctx,ctx.matchCase())
        for case in cases:
            for k in self.all_states():
                self.Assert(z3.If(case.isPresent(k),
                                  result(k) == case.value(case(k)),
                                  True), debug=False)
        self.visitChildren(ctx)


    def visitMatch(self, ctx:ThoriumParser.MatchContext):
        result,expr= self.getRVs(ctx, ctx.expr())
        self.expr_for_match = expr
        cases, = self.getRVs(ctx.matchCases())
        if result.isStream():
            result.setNothing(self.k0-1)
            for k in self.streaming_states():
                result.condSet(k,
                               z3.And(expr.isActive(k),
                                      cases.isActive(k)),
                               cases[k])
        else:
            #TODO: handle this
            pass
        self.visitChildren(ctx)

    def visitStreamMatches(self, ctx:ThoriumParser.StreamMatchesContext):
        result,instance = self.getRVs(ctx, ctx.expr())
        result.setNothing(self.k0-1)
        type_name = ctx.ID().getText()
        type_parts = type_name.split('::')
        base_type = '::'.join(type_parts[:-1])
        z3_type = self.z3_types(base_type)
        case_checker = z3_type.__getattribute__(f'is_{type_name}')
        for k in self.streaming_states():
            result.condSet(k,
                           z3.And(instance.isActive(k),
                                  case_checker(instance[k])),
                           instance[k], debug=True)
        self.visit(ctx.expr())

    def visitMemberAccess(self, ctx: ThoriumParser.MemberAccessContext):
        global TRACES
        result = self[self.expr_name(ctx)]
        composite = self[self.expr_name(ctx.expr())]
        member_name = ctx.ID().getText()
        accessor = self.getMemberAccessor(composite, member_name)
        if isinstance(self.composite_types[str(composite.thorium_type.type)],ReactorType):
            traces = TRACES[str(composite.thorium_type.type)]
            if composite.isStream():
                result.setNothing(self.k0-1)
                for k in self.streaming_states():
                    result.condSet(k, composite.isActive(k), accessor(traces[composite[k]][k]))
            else:
                for k in self.all_states():
                    result.set(k, accessor(traces[composite[k]][k]))
        else:
            if composite.isStream():
                result.setNothing(self.k0-1)
                for k in self.streaming_states():
                    result.condSet(k, composite.isActive(k), accessor(composite[k]))
            else:
                for k in self.all_states():
                    result.set(k, accessor(composite[k]))
        self.visit(ctx.expr())

    def visitPrev(self, ctx:ThoriumParser.PrevContext):
        id = self[ctx.ID().getText()]
        result = self[self.expr_name(ctx)]
        result.setValue(self.k0-1, self.k0-1)
        for k in range(self.k0, self.kK+1):
            result.setValue(k, id(k-1))

    def visitId(self, ctx: ThoriumParser.IdContext):
        id = self[ctx.ID().getText()]
        result = self[self.expr_name(ctx)]
        for k in self.all_states():
            result.set(k, id(k))
        self.visitChildren(ctx)

    def visitNumber(self, ctx: ThoriumParser.NumberContext):
        value = int(ctx.NUMBER().getText())
        result = self[self.expr_name(ctx)]
        for k in self.all_states():
            result.setValue(k, value)
        self.visitChildren(ctx)

    def visitUnitConst(self, ctx:ThoriumParser.UnitConstContext):
        (result,) = self.getRVs(ctx)
        unit = self.z3_types('unit')
        for k in self.all_states():
            result.set(k, unit.unit)


    def visitBool(self, ctx: ThoriumParser.BoolContext):
        (result,) = self.getRVs(ctx)
        for k in self.all_states():
            result.set(k, bool(ctx.TRUE()))
        self.visitChildren(ctx)

    def __getitem__(self, id: str):
        if id in self.local_scope:
            id = self.local_scope[id]
            thorium_type = self.reactor_type.getType(id)
            return ReactiveValue(self.solver,
                                 self.trace,
                                 self.z3_reactor_type.__getattribute__(id),
                                 thorium_type,
                                 self.getZ3Type(thorium_type))
        if self.reactor_type.hasMember(id):
            thorium_type = self.reactor_type.getType(id)
            return ReactiveValue(self.solver,
                                 self.trace,
                                 self.z3_reactor_type.__getattribute__(id),
                                 thorium_type,
                                 self.getZ3Type(thorium_type))
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

    def getThoriumType(self, thorium_type):
        from reactivetypes import Stream, Cell, Optional
        parts = thorium_type.split('-')
        if parts[-1] in self.composite_types:
            composite_type = self.composite_types[parts[-1]]
            if parts[0]=='stream':
                return Stream(composite_type)
            if parts[0]=='cell':
                return Cell(composite_type)
            if parts[0]=='optional':
                return Optional(composite_type)
            return composite_type
        return thorium_type

    def getZ3Type(self, thorium_type):
        from thorium.reactivetypes import Stream, Cell, Optional
        if isinstance(thorium_type,str):
            thorium_type = self.getThoriumType(thorium_type)
        if isinstance(thorium_type, Stream):
            if isinstance(thorium_type.type, str):
                thorium_type.type = self.getThoriumType(thorium_type.type)
            if isinstance(thorium_type.type, ReactorType):
                return self.z3_types('stream-int')
        if isinstance(thorium_type, Cell):
            if isinstance(thorium_type.type, str):
                thorium_type.type = self.getThoriumType(thorium_type.type)
            if isinstance(thorium_type.type, ReactorType):
                return self.z3_types('int')
        if isinstance(thorium_type, Optional):
            if isinstance(thorium_type.type, str):
                thorium_type.type = self.getThoriumType(thorium_type.type)
            if isinstance(thorium_type.type, ReactorType):
                return self.z3_types('optional-int')
        if isinstance(thorium_type, ReactorType):
            return self.z3_types('int')
        return self.z3_types(thorium_type)

    def unit(self,args,result):
        for k in self.streaming_states():
            active = z3.And(*[arg.isActive(k) for arg in args])
            unit = self.z3_types('unit')
            result.condSet(k, active, unit.unit)

    def active(self,args,result):
        for k in self.all_states():
            missing_args = z3.Or(*[arg.isNothing(k) for arg in args])
            result.setValue(k, z3.Not(missing_args))

    def inactive(self,args,result):
        for k in self.all_states():
            missing_args = z3.Or(*[arg.isNothing(k) for arg in args])
            result.setValue(k, missing_args)

    def constructReactor(self,
                         name: str,
                         reactortype: ReactorType,
                         args: List[ReactiveValue],
                         result: ReactiveValue,
                         start_state: int):
        definer = ReactorDefiner(self.composite_types, self.functions, self.z3_types)
        instancename = f'{name}-{reactortype.name}-{start_state}'
        definer(instancename, reactortype.name, start_state, self.final_state, self.solver)
        result[start_state]=definer.trace_ID
        print(f'\n\nConstructing {name} at time {start_state}\n')
        for param,arg in zip([definer[name] for name in reactortype.getParamNames()],args):
            #print(f'param: {param(0)} arg: {arg(0)}')
            print(f'param is stream {param.isStream()} arg is stream {arg.isStream()}')
            if arg.isStream() and not param.isStream():
                for k in range(start_state, self.final_state+1):
                    self.Assert(param(k)==arg[start_state],debug=True)
            else:
                for k in range(start_state, self.final_state+1):
                    self.Assert(param(k)==arg(k),debug=True)
            if param.isStream():
                self.Assert(param.isNothing(self.k0-1))
            else:
                self.Assert(param(start_state-1)==param(start_state),debug=True)

    def visitApply(self, ctx: ThoriumParser.ApplyContext):
        args = [self[self.expr_name(expr)] for expr in ctx.expr()]
        result = self[self.expr_name(ctx)]
        if ctx.ID().getText()=='unit':
            from thorium.snapshot_trigger import SnapshotTrigger
            SnapshotTrigger(self).visitChildren(ctx)
            self.unit(args,result)
        elif ctx.ID().getText()=='active':
            from thorium.snapshot_trigger import SnapshotTrigger
            SnapshotTrigger(self).visitChildren(ctx)
            self.active(args,result)
        elif ctx.ID().getText()=='inactive':
            from thorium.snapshot_trigger import SnapshotTrigger
            SnapshotTrigger(self).visitChildren(ctx)
            self.inactive(args,result)
        else:
            callable = self[ctx.ID().getText()]
            if isinstance(callable, ReactorType):
                for k in range(self.k0, self.kK+1):
                    self.constructReactor(self.expr_name(ctx), callable, args, result, k)
            else:
                self.apply(callable, args, result)
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
        result.setNothing(self.k0-1)
        for k in self.streaming_states():
            result.condSet(k, expr[k] != expr[k - 1], expr[k])
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
        #TODO: simplify, the stream should always be nothing at k0-1
        result.setNothing(self.k0-1)
        for k in self.streaming_states():
            result.condSet(k, stream.isActive(k), cell[k])

    def visitSnapshot(self, ctx: ThoriumParser.SnapshotContext):
        result, (cell, stream) = self.getRVs(ctx, ctx.expr())
        self.snapshot(result, cell, stream)
        self.visit(ctx.expr(0))
        from thorium.snapshot_trigger import SnapshotTrigger
        SnapshotTrigger(self).visit(ctx.expr(1))

    def merge(self, result, s1, s2):
        #TODO: simplify, the stream should always be nothing at k0-1
        result[self.k0-1] = result.nothing
        for k in self.streaming_states():
            result.set(k, z3.If(s1.isNothing(k), s2(k), s1(k)))

    def visitMerge(self, ctx: ThoriumParser.MergeContext):
        result, (s1, s2) = self.getRVs(ctx, ctx.expr())
        self.merge(result, s1, s2)
        self.visitChildren(ctx)

    def filter(self, result, value, condition):
        #TODO: simplify, the value should always be nothing at k0-1
        result[self.k0-1] = result.nothing
        for k in self.streaming_states():
            active = z3.And(condition.isActive(k),
                            value.isActive(k),
                            condition[k])
            result.condSet(k, active, value[k])

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
        #result.setValue(self.k0-1, init(self.k0))
        result[self.k0-1] = init[self.k0]
        for k in self.streaming_states():
            result[k] = z3.If(update.isNothing(k),
                              result[k-1],
                              update[k])

    def visitHold(self, ctx: ThoriumParser.HoldContext):
        result, (init, update) = self.getRVs(ctx, ctx.expr())
        self.hold(result, init, update)
        self.visitChildren(ctx)
