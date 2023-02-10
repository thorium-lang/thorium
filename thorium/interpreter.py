class ReactiveValue:
    def __init__(self, value):
        self.value = value
        self.has_value = True
    def has_value(self):
        return self.has_value
    def value(self):
        return self.value
    def update(self):
        return False
    def finalize(self): pass

class Cell(ReactiveValue): 
    def __init__(self, value):
        ReactiveValue.__init__(self, value)
        self.prev_value = value
    def finalize(self):
        self.prev_value = self.value

class Stream(ReactiveValue):
    def __init__(self):
        self.value = None
        self.has_value = False
    def initialize(self): 
        pass
    def finalize(self): 
        # streams are emptied after every transaction
        self.value = None
        self.has_value = False

class Const(Cell):
    def __init__(self, value):
        self.value = value
        self.has_value = True

class ConstStream(Stream):
    def __init__(self, value):
        self.value = value
        self.has_value = True

class Snapshot(Stream):
    def __init__(self,ID):
        self.ID = ID
        Stream.__init__(self)
    def define(self, cell, stream):
        self.cell   = cell
        self.stream = stream
    def update(self):
        self.has_value = self.stream.has_value
        self.value = self.cell.value
        if self.has_value:
            print(f'snapshot {self.ID} became {self.value}')
        else:
            print(f'snapshot {self.ID} has no value')

class Hold(Cell):
    def __init__(self,ID):
        self.ID = ID
        Cell.__init__(self,None)
    def define(self, init, changes):
        self.init = init
        self.changes = changes
    def initialize(self):
        self.value = self.init.value
        print(f'hold {self.ID} initialized to {self.value}')
    def update(self):
        self.has_value = self.changes.has_value
        print(f'hold {self.ID} unchanged')
        if self.has_value:
            self.value = self.changes.value
            print(f'hold {self.ID} updated to {self.value}')

def apply(f,args):
    return f(*args)

class LiftCell(Cell):
    def __init__(self):
        Cell.__init__(self, None)
    def define(self, f, args):
        self.f = f
        self.args = args
        Cell.__init__(self, apply(f,[arg.value for arg in args]))
    def initialize(self):
        self.update()
    def update(self):
        print(f'lifting {f} with {[arg.value for arg in args]}')
        self.value = apply(f,[arg.value for arg in args])

class LiftStream(Stream):
    def __init__(self, ID):
        self.ID = ID
        Stream.__init__(self)
    def define(self, f, args):
        self.f = f
        self.args = args
    def update(self):
        self.has_value = all(arg.has_value for arg in self.args)
        if self.has_value:
            self.value = apply(self.f,[arg.value for arg in self.args])
            print(f'lift {self.ID}: {self.f} with {[arg.value for arg in self.args]} -> {self.value}')
        else:
            print(f'lift {self.ID} has no value')

class FilterStream(Stream):
    def __init__(self):
        Stream.__init__(self)
    def define(self, value, condition):
        self.value_expr = value
        self.condition = condition
    def update(self):
        self.has_value = self.condition.has_value and self.condition.value
        if self.has_value:
            self.value = self.value_expr.value

class Reactor:
    def __init__(self):
        self.members = []

    def add_member(self, member):
        self.members.append(member)

    def initialize(self):
        for member in self.members:
            member.initialize()

    def update(self):
        for member in self.members:
            member.update()

    def finalize(self):
        for member in self.members:
            member.finalize()
