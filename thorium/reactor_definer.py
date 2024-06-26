from thorium import ThoriumVisitor, ThoriumParser
from thorium.z3types import Z3Types
from thorium.operators import Operators
from typing import List
import z3
from z3 import If,And,Or,Not,Implies
from thorium.reactivetypes import ReactiveValue
from thorium.reactivetypes import base_type
from thorium.decls import StructType, ReactorType

TRACES = {}

UUID = 1001

class TraceHeap:
    def __init__(self, typename, z3_reactor_type):
        self.N = 0
        self.typename = typename
        self.traces = z3.Array(f'{typename}-heap',z3.IntSort(), z3.ArraySort(z3.IntSort(), z3_reactor_type))
        self.first_state_for_trace = []

    def allocate_trace(self, first_state):
        self.first_state_for_trace.append(first_state)
        n = self.N
        self.N += 1
        return n,self.traces[n]

    def __getitem__(self, n):
        return self.traces[n]

    def getFirstStateForTrace(self, n):
        return self.first_state_for_trace[n]

class Constant:
    def __init__(self, value):    self.value = value
    def __getitem__(self, index): return self.value
    def __call__(self, index):    return self.value

    def isStream(self):    return False
    def isActive(self, _): return True

class ReactorDefiner(ThoriumVisitor):
    def __init__(self, composite_types: dict, functions: dict, z3_types: Z3Types):
        ThoriumVisitor.__init__(self)
        self.solver = None
        self.condition = None
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
        self.const_def = False
        self.debug_assert = False

    def const_context(definer):
        class ConstContext:
            def __enter__(self):
                definer.const_def = True
            def __exit__(self, exc_type, exc_val, exc_tb):
                definer.const_def = False
        return ConstContext()

    def condition_context(definer, condition):
        class ConditionContext:
            def __enter__(self):
                definer.condition = condition
            def __exit__(self, exc_type, exc_val, exc_tb):
                definer.condition = None
        return ConditionContext()

    def debug_context(definer):
        class DebugContext:
            def __enter__(self):
                print('='*80)
                definer.debug_assert = True
            def __exit__(self, exc_type, exc_val, exc_tb):
                print('+'*80)
                definer.debug_assert = False
        return DebugContext()

    def expr_name(self, ctx):
        return self.reactor_type.expr_name(ctx)

    def all_states(self, const_def=False):
        if const_def: return [self.first_state]
        return range(self.first_state-1, self.final_state+1)

    def streaming_states(self, const_def=False):
        if const_def: return [self.first_state]
        return range(self.first_state, self.final_state+1)

    def AssertAll(self, statements, debug=False):
        for statement in statements:
            self.Assert(statement, debug)

    def Assert(self, statement, debug=False):
        #print(80*'=')
        #print(statement)
        if debug or self.debug_assert:
            print(statement)
        if self.solver.condition is not None:
            #print(Implies(self.solver.condition, statement))
            #return self.solver.add(Implies(self.solver.condition, statement))
            return self.solver.add(If(self.solver.condition, statement,True))
        else:
            return self.solver.add(statement)

    def apply(self, f: callable,
              args: List[ReactiveValue],
              result: ReactiveValue):
        for k in self.all_states(self.const_def):
            active = And(*[arg.isActive(k) for arg in args])
            self.Assert(If(active,
                           result.set(k,f(*[arg[k] for arg in args])),
                           result.isNothing(k)))

    def get_trace(self, index):
        global TRACES
        heap = TRACES[self.typename]
        return heap[index]

    def create_trace(self, first_state):
        global TRACES
        if self.typename not in TRACES:
            TRACES[self.typename] = TraceHeap(self.typename, self.z3_reactor_type)
        return TRACES[self.typename].allocate_trace(first_state)

    def __call__(self, name: str, typename: str, first_state: int, final_state: int, solver: z3.Solver):
        self.typename = typename
        self.reactor_type = self.composite_types[typename]
        self.z3_reactor_type = self.z3_types(typename)
        #self.trace = z3.Array(name,z3.IntSort(), self.z3_reactor_type)
        self.trace_ID, self.trace = self.create_trace(first_state)
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
        return composite_z3_type.__getattribute__(member_name)

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
                    self.Assert(arg_member.set(k,accessor(instance[k])))

        result,value = self.getRVs(ctx, ctx.expr())

        def condition(k):
            return And(instance.isActive(k), case_checker(instance[k]))

        for k in self.streaming_states():
            self.Assert(If(condition(k),
                           result(k) == value(k),
                           #result.set(k,value[k]),
                           result.isNothing(k)))

        with self.condition_context(condition):
            self.visitChildren(ctx)
        self.local_scope = {}

    def visitMatchCases(self, ctx:ThoriumParser.MatchCasesContext):
        result,cases = self.getRVs(ctx,ctx.matchCase())
        cases = list(cases)
        cases.reverse()
        for k in self.all_states():
            assertion = result.isNothing(k)
            for case in cases:
                assertion = If(case.isActive(k),
                               result(k) == case(k),
                               assertion)
            self.Assert(assertion)
        self.visitChildren(ctx)


    def visitMatch(self, ctx:ThoriumParser.MatchContext):
        result,expr= self.getRVs(ctx, ctx.expr())
        self.expr_for_match = expr
        cases, = self.getRVs(ctx.matchCases())
        if result.isStream():
            self.Assert(result.isNothing(self.k0-1))
            for k in self.streaming_states():
                self.Assert(If(And(expr.isActive(k), cases.isActive(k)),
                                   result(k) == cases(k),
                                   result.isNothing(k)))
        else:
            for k in self.all_states():
                self.Assert(Implies( cases.isActive(k), result[k] == cases[k]))
        self.visitChildren(ctx)

    def visitStreamMatches(self, ctx:ThoriumParser.StreamMatchesContext):
        result,instance = self.getRVs(ctx, ctx.expr())
        self.Assert(result.isNothing(self.k0-1))
        type_name = ctx.ID().getText()
        type_parts = type_name.split('::')
        base_type = '::'.join(type_parts[:-1])
        z3_type = self.z3_types(base_type)
        case_checker = z3_type.__getattribute__(f'is_{type_name}')
        for k in self.streaming_states():
            self.Assert(If(And(instance.isActive(k),
                               case_checker(instance[k])),
                           result.set(k,instance[k]),
                           result.isNothing(k)))
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
                self.Assert(result.isNothing(self.k0-1))
                for k in self.streaming_states():
                    self.Assert(If(composite.isActive(k),
                                   result.set(k,accessor(traces[composite[k]][k])),
                                   result.isNothing(k)))
            else:
                for k in self.all_states():
                    self.Assert(result(k) == accessor(traces[composite[k]][k]))
        else:
            if composite.isStream():
                self.Assert(result.isNothing(self.k0-1))
                for k in self.streaming_states():
                    self.Assert(If(composite.isActive(k),
                                   result.set(k,accessor(composite[k])),
                                   result.isNothing(k)))
            else:
                for k in self.all_states():
                    self.Assert(result(k) == accessor(composite[k]))
        self.visit(ctx.expr())

    def visitPrev(self, ctx:ThoriumParser.PrevContext):
        id = self[ctx.ID().getText()]
        result = self[self.expr_name(ctx)]
        for k in range(self.k0, self.kK+1):
            self.Assert(result[k] == id[k - 1])

    def visitUnitConst(self, ctx:ThoriumParser.UnitConstContext):
        (result,) = self.getRVs(ctx)
        unit = self.z3_types('unit')
        for k in self.all_states():
            self.Assert(result(k)==unit.unit)


    def visitBool(self, ctx: ThoriumParser.BoolContext):
        (result,) = self.getRVs(ctx)
        for k in self.all_states():
            self.Assert(result(k)==bool(ctx.TRUE()))
        self.visitChildren(ctx)

    def __getitem__(self, id: str):
        if id in self.reactor_type.constants:
            return Constant(self.reactor_type.constants[id])
        if id in self.reactor_type.id_refs:
            #print(f'Returning id reference for {id} {self.reactor_type.id_refs[id]} {self[self.reactor_type.id_refs[id]]}')
            return self[self.reactor_type.id_refs[id]]
        if id in self.local_scope:
            id = self.local_scope[id]
            thorium_type = self.reactor_type.getType(id)
            return ReactiveValue(self.trace,
                                 self.z3_reactor_type.__getattribute__(id),
                                 thorium_type,
                                 self.getZ3Type(thorium_type))
        if self.reactor_type.hasMember(id):
            thorium_type = self.reactor_type.getType(id)
            return ReactiveValue(self.trace,
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
        prefix = '::'.join(id.split('::')[:-1])
        if prefix in self.composite_types:
            enum = self.composite_types[prefix]
            return enum.constructor(id.split('::')[-1])

    def getThoriumType(self, thorium_type):
        from reactivetypes import Stream, Cell
        parts = thorium_type.split('-')
        if parts[-1] in self.composite_types:
            composite_type = self.composite_types[parts[-1]]
            if parts[0]=='stream':
                return Stream(composite_type)
            if parts[0]=='cell':
                return Cell(composite_type)
            return composite_type
        return thorium_type

    def getZ3Type(self, thorium_type):
        from thorium.reactivetypes import Stream, Cell
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
        if isinstance(thorium_type, ReactorType):
            return self.z3_types('int')
        return self.z3_types(thorium_type)

    def unit(self,args,result):
        for k in self.streaming_states():
            active = And(*[arg.isActive(k) for arg in args])
            unit = self.z3_types('unit')
            self.Assert(If(active,
                           result.set(k,unit.unit)),
                           result.isNothing(k))

    def active(self,args,result):
        for k in self.all_states():
            missing_args = Or(*[arg.isNothing(k) for arg in args])
            self.Assert(result[k] == Not(missing_args))

    def inactive(self,args,result):
        for k in self.all_states():
            missing_args = Or(*[arg.isNothing(k) for arg in args])
            self.Assert(result[k] == missing_args)

    def constructReactor(self,
                         name: str,
                         reactortype: ReactorType,
                         args: List[ReactiveValue],
                         result: ReactiveValue,
                         start_state: int):
        definer = ReactorDefiner(self.composite_types, self.functions, self.z3_types)
        instancename = f'{name}-{reactortype.name}-{start_state}'
        trigger_args = [arg for param,arg in zip([reactortype.getType(name) for name in reactortype.getParamNames()],args)
                        if arg.isStream() and not param.isStream()]
        if trigger_args:
            inactive = Or(*[arg.isNothing(start_state) for arg in trigger_args])
            active = And(*[arg.isActive(start_state) for arg in trigger_args])
        else:
            inactive = False
            active = True
        if self.condition:
            self.solver.condition = And(self.condition(start_state), active)
        else:
            self.solver.condition = active
        definer(instancename, reactortype.name, start_state, self.final_state, self.solver)
        self.solver.condition = None
        self.Assert(If(inactive,
                       result.isNothing(start_state),
                       result.set(start_state,definer.trace_ID)))
        #print(f'\n\nConstructing {name} at time {start_state}\n')
        for param,arg in zip([definer[name] for name in reactortype.getParamNames()],args):
            #print(f'param: {param(0)} arg: {arg(0)}')
            #print(f'param is stream {param.isStream()} arg is stream {arg.isStream()}')
            if arg.isStream() and not param.isStream():
                for k in range(start_state, self.final_state+1):
                    self.Assert(param[k] == arg[start_state])
            else:
                for k in range(start_state, self.final_state+1):
                    self.Assert(param(k) == arg(k))
            if param.isStream():
                self.Assert(param.isNothing(self.k0-1))
            else:
                self.Assert(param(start_state-1)==param(start_state))

    def visitApply(self, ctx: ThoriumParser.ApplyContext):
        args = [self[self.expr_name(expr)] for expr in ctx.expr()]
        result = self[self.expr_name(ctx)]
        if ctx.ID().getText()=='unit':
            #from thorium.snapshot_trigger import SnapshotTrigger
            #SnapshotTrigger(self).visitChildren(ctx)
            self.visitChildren(ctx)
            self.unit(args,result)
        elif ctx.ID().getText()=='active':
            #from thorium.snapshot_trigger import SnapshotTrigger
            #SnapshotTrigger(self).visitChildren(ctx)
            self.visitChildren(ctx)
            self.active(args,result)
        elif ctx.ID().getText()=='inactive':
            #from thorium.snapshot_trigger import SnapshotTrigger
            #SnapshotTrigger(self).visitChildren(ctx)
            self.visitChildren(ctx)
            self.inactive(args,result)
        elif ctx.ID().getText()=='uuid':
            global UUID
            if self.const_def:
                uuid = UUID
                UUID += 1
                for k in self.all_states():
                    self.Assert(result[k] == uuid)
            else:
                for k in self.all_states():
                    uuid = UUID
                    UUID += 1
                    self.Assert(result[k] == uuid)
        else:
            callable = self[ctx.ID().getText()]
            if isinstance(callable, ReactorType):
                if self.const_def:
                    self.constructReactor(self.expr_name(ctx), callable, args, result, self.k0)
                else:
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
        self.Assert(result.isNothing(self.k0-1))
        for k in self.streaming_states():
            self.Assert(If(expr[k] != expr[k - 1],
                           result.set(k,expr[k]),
                           result.isNothing(k)))
        self.visitChildren(ctx)

    def visitParen(self, ctx:ThoriumParser.ParenContext):
        child = ctx.expr()
        if(isinstance(child,ThoriumParser.IdContext)):
            id = self[child.ID().getText()]
            result, = self.getRVs(ctx)
            for k in self.all_states():
                self.Assert(result(k) == id(k))
        self.visitChildren(ctx)

    def visitLtlParen(self, ctx:ThoriumParser.LtlParenContext):
        child = ctx.ltlProperty()
        if(isinstance(child,ThoriumParser.IdContext)):
            id = self[child.ID().getText()]
            result, = self.getRVs(ctx)
            for k in self.all_states():
                self.Assert(result(k) == id(k))
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
        self.Assert(result.isNothing(self.k0-1))
        for k in self.streaming_states():
            self.Assert(If(stream.isActive(k),
                           result.set(k,cell[k]),
                           result.isNothing(k)))

    def visitSnapshot(self, ctx: ThoriumParser.SnapshotContext):
        result, (cell, stream) = self.getRVs(ctx, ctx.expr())
        self.AssertAll(snapshot(self.k0, self.kK, result, cell, stream))
        with self.condition_context(lambda k: stream.isActive(k)):
            self.visit(ctx.expr(0))
        #from thorium.snapshot_trigger import SnapshotTrigger
        #SnapshotTrigger(self).visit(ctx.expr(1))
        self.visitChildren(ctx)

    def merge(self, result, s1, s2):
        self.Assert(result.isNothing(self.k0-1))
        for k in self.streaming_states():
            self.Assert(result(k)==If(s1.isNothing(k), s2(k), s1(k)))

    def visitMerge(self, ctx: ThoriumParser.MergeContext):
        result, (s1, s2) = self.getRVs(ctx, ctx.expr())
        self.AssertAll(merge(self.k0, self.kK, result, s1, s2))
        self.visitChildren(ctx)

    def filter(self, result, value, condition):
        self.Assert(result.isNothing(self.k0-1))
        for k in self.streaming_states():
            active = And(condition.isActive(k),
                         value.isActive(k),
                         condition[k])
            self.Assert(If(active,
                           result.set(k,value[k]),
                           result.isNothing(k)))

    def visitFilter(self, ctx: ThoriumParser.FilterContext):
        result, (value, condition) = self.getRVs(ctx, ctx.expr())
        self.AssertAll(filter(self.k0, self.kK, result, value, condition))
        self.visitChildren(ctx)

    def getRVs(self,*args):
        for arg in args:
            if isinstance(arg, list) or isinstance(arg, tuple):
                yield list(self.getRVs(*arg))
            else:
                yield self[self.expr_name(arg)]

    def hold(self, result, init, update):
        self.Assert(result[self.k0 - 1] == init[self.k0])
        for k in self.streaming_states():
            self.Assert(
                result[k] == If(update.isNothing(k),
                                result[k-1],
                                update[k]))

    def visitHold(self, ctx: ThoriumParser.HoldContext):
        result, (init, update) = self.getRVs(ctx, ctx.expr())
        #with self.debug_context():
        self.AssertAll(hold(self.k0, self.kK, result, init, update))
        init,update = ctx.expr()
        with self.const_context():
            self.visit(init)
        self.visit(update)

    def visitReactorMember(self, ctx:ThoriumParser.ReactorMemberContext):
        result, = self.getRVs(ctx.expr())
        if ctx.reactiveType().CONST():
            with self.const_context():
                self.visitChildren(ctx)
                for k in self.streaming_states():
                    self.Assert(result[k] == result[self.k0])
        else:
            self.visitChildren(ctx)

def hold(k0     : int, # initial state
         kK     : int, # final state
         result : ReactiveValue,
         init   : ReactiveValue,
         update : ReactiveValue):
    yield result[k0-1] == init[k0]
    for k in range(k0, kK+1):
        yield result[k] == If(update.isNothing(k),
                              result[k-1],
                              update[k])

def filter(k0        : int, # initial state
           kK        : int, # final state
           result    : ReactiveValue,
           value     : ReactiveValue,
           condition : ReactiveValue):
    yield result.isNothing(k0-1) # streams are empty during init
    for k in range(k0, kK+1):
        active = And(condition.isActive(k),
                     value.isActive(k),
                     condition[k])
        yield If(active,
                 result.set(k,value[k]),
                 result.isNothing(k))

def snapshot(k0        : int, # initial state
             kK        : int, # final state
             result    : ReactiveValue,
             cell      : ReactiveValue,
             stream    : ReactiveValue):
    yield result.isNothing(k0-1)
    for k in range(k0, kK+1):
        yield If(stream.isNothing(k),
                 result.isNothing(k),
                 result.set(k,cell[k]))

def merge(k0     : int, # initial state
          kK     : int, # final state
          result : ReactiveValue,
          s1     : ReactiveValue,
          s2     : ReactiveValue):
    yield result.isNothing(k0-1)
    for k in range(k0, kK+1):
        yield result(k) == If(s1.isNothing(k),
                                 s2(k),
                                 s1(k))
