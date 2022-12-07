import z3

CoordSort = z3.Datatype('CoordSort')
WaypointSort = z3.Datatype('WaypointSort')
PathSort = z3.Datatype('PathSort')
GeoAreaSort = z3.Datatype('GeoAreaSort')

CoordSort.declare('Coord', ('latitude',  z3.RealSort()), 
                           ('longitude', z3.RealSort()))

WaypointSort.declare('Waypoint', ('label',    z3.StringSort()),
                                 ('location', z3.StringSort()))

