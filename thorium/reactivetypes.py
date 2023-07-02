import z3

class Cell:
    def __init__(self, type_):
        if isinstance(type_, Stream) or isinstance(type_, Cell):
            self.type = type_.type
        else:
            self.type = type_

    def __str__(self):
        return f'cell-{self.type}'


class Stream:
    def __init__(self, type_):
        if isinstance(type_, Stream) or isinstance(type_, Cell):
            self.type = type_.type
        else:
            self.type = type_
        self.name = self

    def declareZ3Constructor(self, type_ctx):
        type_ctx(self).declare('event', ('value', type_ctx(self.type)))
        type_ctx(self).declare('nothing')

    def __str__(self):
        return f'stream-{self.type}'

    def __eq__(self, other):
        return isinstance(other, Stream) and (self.type == other.type)

class ReactiveValue:
    def __init__(self, trace, accessor, thorium_type, z3_type):
        self.trace = trace
        self.accessor = accessor
        self.thorium_type = thorium_type
        self.z3_type = z3_type

    def __call__(self, k):
        return self.accessor(self.trace[k])

    def isStream(self):
        return isinstance(self.thorium_type, Stream)

    def isNothing(self, k):
        if self.isStream():
            return self(k) == self.z3_type.nothing
        return False

    def isTrue(self, k):
        if self.isStream():
            return z3.If(self.isNothing(k), False, self[k])
        return self(k)

    def __setitem__(self, k, value):
        if self.isStream():
            return self(k) == self.z3_type.event(value)
        return self(k) == value

    def __getitem__(self,k):
        # special case, 'unit' presence is treated as True
        if self.thorium_type == Stream('unit'):
            return z3.Not(self.isNothing(k))
        if self.isStream():
            return self.z3_type.value(self(k))
        return self(k)

    #def __repr__(self):
    #return f'{self.accessor}:{self.thorium_type}({self.z3_type})'


def base_type(type_):
    if isinstance(type_, Cell):
        return type_.type
    if isinstance(type_, Stream):
        return type_.type
    return type_

