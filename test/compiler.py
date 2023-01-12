#!/usr/bin/env python3

import sys
import z3
import antlr4
from thorium import *

class PrintVisitor(ThoriumVisitor):
    def visitReactor(self, ctx:ThoriumParser.ReactorContext):
        params = self.visit(ctx.reactorParams())
        print(f'params: {params}')
        members = [self.visit(m) for m in ctx.reactorMembers()]
        print(f'members: {members}')

    def visitReactorParams(self, ctx:ThoriumParser.ReactorParamsContext):
        return [self.visit(m) for m in ctx.reactorParam()]

    def visitReactorMembers(self, ctx:ThoriumParser.ReactorMembersContext):
        return [self.visit(m) for m in ctx.reactorMember()]

    def visitReactorParam(self, ctx:ThoriumParser.ReactorParamContext):
        return ctx.ID().getText()

    def visitReactorMember(self, ctx:ThoriumParser.ReactorMemberContext):
        return ctx.ID().getText()
        

def main(argv):
    input_stream = antlr4.FileStream(argv[1])
    lexer = ThoriumLexer(input_stream)
    stream = antlr4.CommonTokenStream(lexer)
    parser = ThoriumParser(stream)
    tree = parser.prog();
    #walker = antlr4.ParseTreeWalker()
    visitor = PrintVisitor()
    #walker.walk(visitor, tree)
    visitor.visitProg(tree)

if __name__ == '__main__':
    main(sys.argv)
