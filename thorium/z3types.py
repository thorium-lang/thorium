import z3
from thorium.reactivetypes import Stream
from thorium.reactivetypes import Cell

class Z3Types:
    def __init__(self, debug=False):
        self.debug = debug
        unit = z3.Datatype('unit')
        unit.declare('unit')
        unit = unit.create()
        self.types = {'int': z3.IntSort(),
                      'real': z3.RealSort(),
                      'bool': z3.BoolSort(),
                      'unit': unit}
        self.datatypes = []
        self.addDatatype(Stream('int'))
        self.addDatatype(Stream('real'))
        self.addDatatype(Stream('bool'))
        self.addDatatype(Stream('unit'))

    def addDatatype(self, datatype):
        self.datatypes.append(datatype)
        self.types[str(datatype)] = z3.Datatype(str(datatype))
        if not isinstance(datatype, Stream):
            self.addDatatype(Stream(datatype.name))

    def __call__(self, type_):
        if isinstance(type_, Cell):
            return self(str(type_.type))
            #return self.types[str(type_.type)]
        typename = str(type_)
        parent_typename = '::'.join(typename.split('::')[:-1])
        if typename not in self.types and parent_typename in self.types:
            return self.types[parent_typename]
        return self.types[str(type_)]

    def finalizeDatatypes(self):
        for datatype in self.datatypes:
            datatype.declareZ3Constructor(self)
        datatype_names = [str(dt) for dt in self.datatypes]
        args = [self(name) for name in datatype_names]
        datatypes = z3.CreateDatatypes(*args)
        self.types.update(
            {name: datatype for name, datatype in zip(datatype_names, datatypes)})
        if self.debug:
            for typename in self.types:
                print(f'datatype {typename}')

