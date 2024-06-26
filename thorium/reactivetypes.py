import z3

class Cell:
    def __init__(self, type_):
        if isinstance(type_, Stream) or isinstance(type_, Cell):
            self.type = type_.type
        else:
            self.type = type_

    def __str__(self):
        return f'cell-{self.type}'

    def isStream(self): return False

class Const(Cell): pass

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

    def isStream(self): return True

class ReactiveValue:
    def __init__(self, trace, accessor, thorium_type, z3_type):
        self.trace = trace               # the reactor trace
        self.accessor = accessor         # access the the member of the reactor
        self.thorium_type = thorium_type
        self.z3_type = z3_type
        if self.isStream():
            self.nothing = self.z3_type.nothing

    def isStream(self):
        return isinstance(self.thorium_type, Stream)

    def isNothing(self, k):
        if self.isStream():
            return self.accessor(self.trace[k])==self.nothing
        return False

    def isActive(self, k):
        if self.isStream():
            return self.accessor(self.trace[k])!=self.nothing
        return True

    def isTrue(self, k):
        if self.isStream():
            return z3.If(self.isNothing(k), False, self[k])
        return self(k)

    def set(self, k, value):
        if self.isStream():
            return self(k) == self.z3_type.event(value)
        return self(k) == value

    def __call__(self, k):
        return self.accessor(self.trace[k])

    def __getitem__(self,k):
        i = self.accessor(self.trace[k])
        if self.isStream():
            return self.z3_type.value(i)
        return i


def base_type(type_):
    if isinstance(type_, Cell):
        return type_.type
    if isinstance(type_, Stream):
        return type_.type
    return type_

