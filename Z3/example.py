from z3 import *

List = Datatype('List')
# Constructor cons: (Int, List) -> List
List.declare('cons', ('car', IntSort()), ('cdr', List))
# Constructor nil: List
List.declare('nil')

print is_sort(List)
List = List.create()
print is_sort(List)


Resource = Datatype('Resource')
Request  = Datatype('Request')
Response = Datatype('Response')
Manager  = Datatype('Manager')
Worker   = Datatype('Worker')

Resource.declare('Resource', ('id',        IntSort()))
Request.declare( 'Request',  ('worker_id', IntSort()))
Response.declare('Success',  ('resource',  IntSort()))
Response.declare('ResourceUnavailable')

#Manager.declare( 'Manager',  ('

A = Array('A', IntSort(), ArraySort(IntSort(), IntSort()))
x, y = Ints('x y')
print(A[x][y])
