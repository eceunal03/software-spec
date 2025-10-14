---- MODULE MC ----
EXTENDS lock_single, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxShipsLocation
const_176047791340474000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1NumShips
const_176047791340475000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2NumLocks
const_176047791340476000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3MaxShipsLock
const_176047791340477000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:4defaultInitValue
const_176047791340478000 == 
0
----

\* INIT definition @modelBehaviorNoSpec:0
init_176047791340479000 ==
FALSE/\requests = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_176047791340480000 ==
FALSE/\requests' = requests
----
=============================================================================
\* Modification History
\* Created Tue Oct 14 23:38:33 CEST 2025 by 20241799
