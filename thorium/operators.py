import operator
import z3

class Operators:
    unary = {'-': operator.neg,
             'not': z3.Not}
    binary = {'+': operator.add,
              '-': operator.sub,
              '*': operator.mul,
              '/': operator.truediv,
              '<': operator.lt,
              '<=': operator.le,
              '>': operator.gt,
              '>=': operator.ge,
              '==': operator.eq,
              '!=': operator.ne,
              '->': z3.Implies,
              'and': z3.And,
              'or': z3.Or,
              }
