#!/usr/bin/env python3
import sys
import argparse
import antlr4

import z3
from thorium import ThoriumLexer, ThoriumParser
from thorium.decls import Function
from thorium.reactor_definer import ReactorDefiner
from thorium.parse_declarations import ParseDeclarations
from thorium.typechecking import SubExprTypeCheck
from thorium.z3types import Z3Types
from typing import List


def named_lookup(named_items: List):
    return {t.name: t for t in named_items}


def parse_thorium_file(filename):
    input_stream = antlr4.FileStream(filename)
    lexer = ThoriumLexer(input_stream)
    stream = antlr4.CommonTokenStream(lexer)
    parser = ThoriumParser(stream)
    tree = parser.prog()

    declarations = ParseDeclarations().visitProg(tree)
    SubExprTypeCheck(named_lookup(declarations)).visitProg(tree)
    z3_types = Z3Types()
    composite_types = []
    functions = []
    for declaration in declarations:
        if isinstance(declaration, Function):
            functions.append(declaration)
        else:
            z3_types.addDatatype(declaration)
            composite_types.append(declaration)
    z3_types.finalizeDatatypes()
    for f in functions:
        f.setTypeContext(z3_types)

    return named_lookup(composite_types), named_lookup(functions), z3_types


def main(_argv):
    argparser = argparse.ArgumentParser(prog='thorium-verifier',
                                        description='Verifies reactor properties.')

    argparser.add_argument('filename')
    argparser.add_argument('-r', '--reactor', dest='reactor', required=True)
    argparser.add_argument('-p', '--property', dest='property', required=True)
    argparser.add_argument('-n', '--num-states', dest='N', type=int, required=True)
    argparser.add_argument('-f', '--full-model', dest='full_model', action='store_true', default=False)

    args = argparser.parse_args()

    composite_types, functions, z3_types = parse_thorium_file(args.filename)

    reactor_definer = ReactorDefiner(composite_types, functions, z3_types)
    solver = z3.Solver()
    reactor = reactor_definer(f'{args.reactor}-main', args.reactor, 0, args.N, solver)
    reactor_type = z3_types(args.reactor)
    thorium_reactor = composite_types[args.reactor]

    # print(repr(thorium_reactor))

    property_ = reactor_type.__getattribute__(args.property)

    solver.add(z3.Not(property_(reactor[0])))

    verification_result = solver.check()

    # print(solver.statistics())
    # print(solver.statistics().keys())

    print(f"Time      : {solver.statistics().get_key_value('time')} seconds")
    print(f"Max memory: {solver.statistics().get_key_value('max memory')}")

    if verification_result == z3.sat:
        z3_trace = solver.model()[reactor]
        #f = {a.as_long(): b for a, b in z3_trace.as_list()[:-1]}
        trace = []
        if args.full_model:
            namegetter = thorium_reactor.getMemberNames
            getter = thorium_reactor.getMemberValues
        else:
            namegetter = thorium_reactor.getDeclaredMemberNames
            getter = thorium_reactor.getDeclaredMemberValues
        for k in range(args.N + 1):
            trace.append(getter(solver.model().eval(z3_trace[k])))

        trace = [namegetter()] + trace
        column_widths = [max([len(name) for name in column]) for column in trace]
        format_string = ' & '.join(('%%%ds' % width) for width in column_widths) + r' \\'
        print(r'\begin{centering}')
        print(r'\begin{tabular}{%s}' % ('|c' * len(column_widths) + '|'))
        print(r'\hline')
        print(format_string % tuple(['k'] + list(range(len(column_widths) - 1))))
        print(r'\hline')
        for row in [[t[i] for t in trace] for i in range(len(trace[0]))]:
            print(format_string % tuple(row))
        print(r'\hline')
        print(r'\end{tabular}\\')
        print(r'\end{centering}')

    if verification_result == z3.unsat:
        print(f'Property "{args.property}" for reactor "{args.reactor}" holds for all runs of {args.N} steps.')


if __name__ == '__main__':
    main(sys.argv)
