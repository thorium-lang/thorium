from thorium import ThoriumParser
from thorium import ThoriumVisitor
import z3
from z3 import If,And,Or,Not

from thorium.reactivetypes import ReactiveValue, base_type
from thorium.reactor_definer import ReactorDefiner

class PropertyDefiner(ReactorDefiner):
    def __init__(self, parent: ReactorDefiner):
        ThoriumVisitor.__init__(self)
        ReactorDefiner.__init__(self, parent.composite_types, parent.functions, parent.z3_types)
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
        self.const_def = parent.const_def
        self.debug_assert = parent.debug_assert

    def visitLtlNegation(self, ctx: ThoriumParser.LtlNegationContext):
        Np, p = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(LtlNot(self.k0, self.kK, Np, p))
        self.visitChildren(ctx)

    def visitNot(self, ctx: ThoriumParser.NotContext):
        Np, p = self.getRVs(ctx, ctx.expr())
        self.AssertAll(LtlNot(self.k0, self.kK, Np, p))
        self.visitChildren(ctx)

    def visitLtlAnd(self, ctx: ThoriumParser.LtlAndContext):
        pAq, (p,q) = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(LtlAnd(self.k0, self.kK, pAq, p, q))
        self.visitChildren(ctx)

    def visitAnd(self, ctx: ThoriumParser.AndContext):
        pAq, (p,q) = self.getRVs(ctx, ctx.expr())
        self.AssertAll(LtlAnd(self.k0, self.kK, pAq, p, q))
        self.visitChildren(ctx)

    def visitLtlOr(self, ctx: ThoriumParser.LtlOrContext):
        pOq, (p,q) = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(LtlOr(self.k0, self.kK, pOq, p, q))
        self.visitChildren(ctx)

    def visitOr(self, ctx: ThoriumParser.AndContext):
        pOq, (p,q) = self.getRVs(ctx, ctx.expr())
        self.AssertAll(LtlOr(self.k0, self.kK, pOq, p, q))
        self.visitChildren(ctx)

    def visitLtlNext(self, ctx:ThoriumParser.LtlNextContext):
        Xp, p = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(next(self.k0, self.kK, Xp, p))
        self.visitChildren(ctx)

    def visitLtlGlobally(self, ctx: ThoriumParser.LtlGloballyContext):
        Gp, p = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(globally(self.k0, self.kK, Gp, p))
        self.visitChildren(ctx)

    def visitLtlEventually(self, ctx: ThoriumParser.LtlEventuallyContext):
        Fp, p = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(eventually(self.k0, self.kK, Fp, p))
        self.visitChildren(ctx)

    def visitLtlPreviously(self, ctx: ThoriumParser.LtlPreviouslyContext):
        Pp, p = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(previously(self.k0, self.kK, Pp, p))
        self.visitChildren(ctx)

    def visitLtlUntil(self, ctx: ThoriumParser.LtlUntilContext):
        pUq, (p, q) = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(until(self.k0, self.kK, pUq, p, q))
        self.visitChildren(ctx)

    def visitLtlSince(self, ctx: ThoriumParser.LtlSinceContext):
        pSq, (p, q) = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(since(self.k0, self.kK, pSq, p, q))
        self.visitChildren(ctx)

    def visitLtlImplication(self, ctx: ThoriumParser.LtlImplicationContext):
        pIq, (p, q) = self.getRVs(ctx, ctx.ltlProperty())
        self.AssertAll(implies(self.k0, self.kK, pIq, p, q))
        self.visitChildren(ctx)

    def visitImplication(self, ctx: ThoriumParser.ImplicationContext):
        pIq, (p, q) = self.getRVs(ctx, ctx.expr())
        self.AssertAll(implies(self.k0, self.kK, pIq, p, q))
        self.visitChildren(ctx)

    #def visitEquals(self, ctx: ThoriumParser.EqualsContext):
    #    print(f'visitEquals {ctx.getText()} {self.expr_name(ctx)}')
    #    result, (p, q) = self.getRVs(ctx, ctx.expr())
    #    if(base_type(p.thorium_type)=='bool'):
    #        for k in self.all_states():
    #            self.Assert(result.set(k,(p.isTrue(k) == q.isTrue(k))))
    #    else:
    #        for k in self.all_states():
    #            self.Assert(result.set(k,(p[k] == q[k])))
    #    self.visitChildren(ctx)

def LtlNot(k0 : int,
           kK : int,
           Np : ReactiveValue,
           p  : ReactiveValue):
    for k in range(k0,kK+1):
        yield Np[k] == Not(p.isTrue(k))

def LtlAnd(k0  : int, # initial state
          kK  : int, # final state
          pAq : ReactiveValue,
          p   : ReactiveValue,
          q   : ReactiveValue):
    for k in range(k0-1, kK+1):
        yield pAq[k] == And(p.isTrue(k), q.isTrue(k))

def LtlOr(k0  : int, # initial state
          kK  : int, # final state
          pOq : ReactiveValue,
          p   : ReactiveValue,
          q   : ReactiveValue):
    for k in range(k0-1, kK+1):
        #yield pOq.set(k,Or(p.isTrue(k), q.isTrue(k)))
        yield pOq[k] == Or(p.isTrue(k), q.isTrue(k))

def implies(k0  : int, # initial state
            kK  : int, # final state
            pIq : ReactiveValue,
            p   : ReactiveValue,
            q   : ReactiveValue):
    for k in range(k0-1, kK+1):
        #yield pIq.set(k,Or(Not(p.isTrue(k)), q.isTrue(k)))
        yield pIq[k] == Or(Not(p.isTrue(k)), q.isTrue(k))

def since(k0  : int, # initial state
          kK  : int, # final state
          pSq : ReactiveValue,
          p   : ReactiveValue,
          q   : ReactiveValue):
    yield Not(pSq[k0 - 1])
    for k in range(k0, kK+1):
        yield pSq[k] == Or(q.isTrue(k), And(p.isTrue(k), pSq[k-1]))

def until(k0  : int, # initial state
          kK  : int, # final state
          pUq : ReactiveValue,
          p   : ReactiveValue,
          q   : ReactiveValue):
    for k in range(k0, kK+1):
        yield pUq[k] == Or(q.isTrue(k), And(p.isTrue(k), pUq[k+1]))
    yield Not(pUq(kK+1))

def globally(k0 : int, # initial state
             kK : int, # final state
             Gp : ReactiveValue,
             p  : ReactiveValue):
    for k in range(k0, kK+1):
        yield Gp[k] == And(p.isTrue(k), Gp[k+1])
    yield Gp[kK+1] # optimistic semantics

def eventually(k0 : int,
               kK : int,
               Fp : ReactiveValue,
               p  : ReactiveValue):
    for k in range(k0,kK+1):
        yield Fp[k] == Or(p.isTrue(k), Fp[k+1])
    yield Not(Fp[kK+1])  # pessimistic semantics

def previously(k0 : int,
               kK : int,
               Pp : ReactiveValue,
               p  : ReactiveValue):
    yield Not(Pp[k0-1])
    for k in range(k0,kK+1):
        yield Pp[k] == Or(p.isTrue(k), Pp[k-1])

def next(k0 : int,
         kK : int,
         Xp : ReactiveValue,
         p  : ReactiveValue):
    for k in range(k0,kK):
        yield Xp[k] == p.isTrue(k+1)
    yield Not(Xp[kK])
