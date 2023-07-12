#!/usr/bin/env python3

import sys
import z3
import antlr4
from thorium import *

class Z3Type:
    def is_datatype(self): return False
    def sort(self):    return self.sort

class BuiltinType(Z3Type):
    def __init__(self,name,sort,constructor):
        self.name = name
        self.sort = sort
        self.constructor = sort
    def create_instance(self,name):
        return self.constructor(name)

class ArrayType(Z3Type):
    def __init__(self,element_type_id,type_environment):
        self.element_type_id = element_type_id
        self.type_environment = type_environment
    def create_instance(self,name):
        sort =  self.type_environment[self.element_type_id].get_sort()
        return z3.Array(name,sort)

class Struct(Z3Type):
    def is_datatype(self): return True
    def __init__(self,name):
        self.name = name
        self.sort = z3.Datatype(name)
    def sort(self): return self.sort
    def add_member(self,member):
        self.members.append(member)
    def latestMember(self):
        return self.members[-1]
    def finalize(self):
        apply(self.sort.declare,
                [ID]+[m.finalize() for m in self.members])

class StructMember:
    def __init__(self,name,type):
        self.name = name
        self.type = type
    def finalilze(self):
        return (self.name,self.type.sort())



def find_datatypes(tree):
    datatypes = { 'Int' : BuiltinType('Int', z3.IntSort(), z3.Int),
                  'Real': BuiltinType('Real',z3.RealSort(),z3.Real),
                  'Bool': BuiltinType('Bool',z3.BoolSort(),z3.Bool)  }
    
    class FindDatatypes(ThoriumListener):
        def __init__(self): pass
        def enterStruct(self, ctx):
            print('found struct',ctx.ID())
            self.datatypes[ctx.ID()] = Struct(ctx.ID())
    
        def enterEnum(self, ctx):
            print('found enum',ctx.ID())
    walker = antlr4.ParseTreeWalker()
    datatypes = FindDatatypes()
    walker.walk(datatypes, tree)
    return datatypes.datatypes

def define_datatypes(tree, datatypes):
    alldatatypes = {'Int' : BuiltinType('Int',z3.IntSort(),z3.Int),
                    'Real': BuiltinType('Real',z3.RealSort(),z3.Real),
                    'Bool': BuiltinType('Bool',z3.BoolSort(),z3.Bool)}
    alldatatypes.update(datatypes)
    class DefineStructs(ThoriumVisitor):
        def visitStruct(self, ctx):
            help(ctx)
            members = [self.visit(m) for m in ctx.structMember]
            ID = str(ctx.ID())
            print("creating struct",ID)
            self.members = []
        def exitStructMember(self, ctx):
            ID = str(ctx.ID())
            print("   adding member",ID,self.membertype)
            self.members.append((ID, self.membertype))
        def exitStruct(self, ctx):
            ID = str(ctx.ID())
            datatype = datatypes[ID]
            apply(datatype.declare,[ID]+self.members)
        def enterType(self, ctx):
            ID = str(ctx.ID())
            self.membertype = alldatatypes[ID]



    walker = antlr4.ParseTreeWalker()
    definitions = DefineStructs()
    walker.walk(definitions, tree)
    print(datatypes.values())
    apply(z3.CreateDatatypes,datatypes.values())
            

def main(argv):
    input_stream = antlr4.FileStream(argv[1])
    lexer = ThoriumLexer(input_stream)
    stream = antlr4.CommonTokenStream(lexer)
    parser = ThoriumParser(stream)
    tree = parser.prog();
    datatypes = find_datatypes(tree)
    define_datatypes(tree,datatypes)

if __name__ == '__main__':
    main(sys.argv)
