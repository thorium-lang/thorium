#!/usr/bin/env python3
import sys
import argparse
import antlr4

import z3
from thorium import ThoriumLexer, ThoriumParser
from thorium.decls import Function, ReactorType
from thorium.reactor_definer import ReactorDefiner, TRACES
from thorium.parse_declarations import ParseDeclarations
from thorium.typechecking import SubExprTypeCheck
from thorium.z3types import Z3Types
from typing import List
import time


def named_lookup(named_items: List):
    return {t.name: t for t in named_items}


def parse_thorium_file(filename, debug=False):
    input_stream = antlr4.FileStream(filename)
    lexer = ThoriumLexer(input_stream)
    stream = antlr4.CommonTokenStream(lexer)
    parser = ThoriumParser(stream)
    tree = parser.prog()

    declarations = ParseDeclarations(debug).visitProg(tree)
    declarations_lookup = named_lookup(declarations)
    for declaration in declarations:
        declaration.setDeclarations(declarations_lookup)
    SubExprTypeCheck(named_lookup(declarations), debug).visitProg(tree)
    z3_types = Z3Types(debug)
    composite_types = []
    functions = []
    for declaration in declarations:
        if isinstance(declaration, Function):
            functions.append(declaration)
        elif isinstance(declaration, ReactorType):
            z3_types.addDatatype(declaration)
            composite_types.append(declaration)
            declaration.setThoriumTypes(composite_types)
        else:
            z3_types.addDatatype(declaration)
            composite_types.append(declaration)
    z3_types.finalizeDatatypes()
    for f in functions:
        f.setTypeContext(z3_types)

    return named_lookup(composite_types), named_lookup(functions), z3_types

def format_trace(N, solver, thorium_reactor, heap, index, full_model=False, LaTeX=False, label=''):
    z3_trace = solver.model()[heap][index]
    #f = {a.as_long(): b for a, b in z3_trace.as_list()[:-1]}
    trace = []
    if full_model:
        namegetter = thorium_reactor.getMemberNames
        getter = thorium_reactor.getMemberValues
    else:
        namegetter = thorium_reactor.getDeclaredMemberNames
        getter = thorium_reactor.getDeclaredMemberValues
    for k in range(N):
        trace.append(getter(solver.model().eval(z3_trace[k])))

    trace = [namegetter()] + trace
    column_widths = [max(2,max([len(name) for name in column])) for column in trace]
    glue = '  '
    terminator = ''
    if LaTeX:
        glue = ' & '
        terminator = r' \\'

    format_string = glue.join(('%%%ds' % width) for width in column_widths) + terminator
    if LaTeX:
        print(r'\begin{centering}')
        if label: print(f'\\textbf{{{label}}}\\\\')
        print(r'\begin{tabular}{%s}' % ('|c' * len(column_widths) + '|'))
        print(r'\hline')
    elif label:
        print(f'\n{label}\n')
    header = format_string % tuple(['k'] + list(range(N)))
    print(header)
    if LaTeX:
        print(r'\hline')
    else:
        print('-'*len(header))
    for row in [[t[i] for t in trace] for i in range(len(trace[0]))]:
        print(format_string % tuple(row))
    if LaTeX:
        print(r'\hline')
        print(r'\end{tabular}\\')
        print(r'\end{centering}')
    else:
        print('-'*len(header))

def main(_argv):
    argparser = argparse.ArgumentParser(prog='thorium-verifier',
                                        description='Verifies reactor properties.')

    argparser.add_argument('filename')
    argparser.add_argument('-r', '--reactor', dest='reactor', required=False)
    argparser.add_argument('-p', '--property', dest='property', required=False)
    argparser.add_argument('-n', '--num-states', dest='N', type=int, required=False)
    argparser.add_argument('-f', '--full-model', dest='full_model', action='store_true', default=False)
    argparser.add_argument('-d', '--debug', dest='debug', action='store_true', default=False)
    argparser.add_argument('-x', '--LaTeX', dest='latex', action='store_true', default=False)

    args = argparser.parse_args()

    composite_types, functions, z3_types = parse_thorium_file(args.filename, debug=args.debug)

    reactor_definer = ReactorDefiner(composite_types, functions, z3_types)
    z3.set_param("smt.random_seed", int(time.time()))
    solver = z3.Solver()
    if args.reactor:
        reactor = reactor_definer(f'{args.reactor}-main', args.reactor, 0, args.N-1, solver)
        reactor_type = z3_types(args.reactor)

        property_ = reactor_type.__getattribute__(args.property)

        solver.add(z3.Not(property_(reactor[0])))

        verification_result = solver.check()

        # print(solver.statistics())
        # print(solver.statistics().keys())

        print(f"Time      : {solver.statistics().get_key_value('time')} seconds")
        print(f"Max memory: {solver.statistics().get_key_value('max memory')}")

        if verification_result == z3.sat:
            reactor_types = [heap.typename for heap in TRACES.values()]
            reactor_types.remove(args.reactor)
            reactor_types.sort()
            reactor_types = [args.reactor] + reactor_types

            for reactor_type in reactor_types:
                reactor_heap = TRACES[reactor_type]
                reactor_traces = reactor_heap.traces
                thorium_reactor = composite_types[reactor_type]
                for n in range(reactor_heap.N):
                    format_trace(args.N, solver, thorium_reactor, reactor_traces, n, args.full_model, LaTeX=args.latex, label=f'{reactor_type}-{n}')

        if verification_result == z3.unsat:
            print(f'Property "{args.property}" for reactor "{args.reactor}" holds for all runs of {args.N} steps.')


if __name__ == '__main__':
    main(sys.argv)
