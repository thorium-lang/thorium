from thorium import *
import thorium
import operator

class Stage: pass

#interface Stage {
#    output: stream Int
#}

'''
reactor Counter(init: Int, clock: stream Unit) : Stage {
    output = value @ clock;

private:
    value  = init .. (value + 1 @ clock);
}
'''

class Counter(Reactor):
    def __init__(self, init, clock):
        self.output = Snapshot('counter.output')

        value      = Hold('value')
        next_value = LiftStream('next_value')
        increment  = Snapshot('increment')

        self.members = [ self.output,
                         increment,
                         next_value,
                         value ]

        self.output.define(value,        clock)
        next_value  .define(operator.add, (value, increment))
        increment   .define(Cell(1),      clock)
        value       .define(init,         next_value)

        self.initialize()
'''
reactor Filter(prime: Int, input: stream Int) : Stage {
    output = input if (input % prime != 0);
}
'''

class Filter(Reactor):
    def __init__(self, prime, input):
        modulo = LiftStream('modulo')
        nonzero = LiftStream('nonzero')
        self.output = FilterStream()

        self.members = [ modulo,
                         nonzero,
                         self.output ]

        modulo.define(operator.mod, [input, prime])
        nonzero.define(operator.ne, [modulo, Const(0)])
        self.output.define(input,nonzero)

        self.initialize()
        

clock = ConstStream(None)

counter = Counter(Cell(2), clock)

filter = Filter(Const(2), counter.output)

for i in range(20):
    counter.update()
    filter.update()

    print(f'counter: {counter.output.value}')
    print(f'filter:  {filter.output.value}')

    counter.finalize()
    filter.finalize()


'''
reactor Sieve(clock: stream Unit) {
    output = curr.output;

private:
    curr: cell Stage = Counter(2,clock) ..
                       Filter(output, curr.output);
properties:
    G is_prime(output);
}
'''
