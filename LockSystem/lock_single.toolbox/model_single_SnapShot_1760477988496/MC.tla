---- MODULE MC ----
EXTENDS lock_single, TLC

\* CONSTANT definitions @modelParameterConstants:0MaxShipsLocation
const_176047798643981000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1NumShips
const_176047798643982000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2NumLocks
const_176047798643983000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3MaxShipsLock
const_176047798643984000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:4defaultInitValue
const_176047798643985000 == 
0
----

\* INIT definition @modelBehaviorNoSpec:0
init_176047798643986000 ==
FALSE/\requests = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_176047798643987000 ==
FALSE/\requests' = requests
----
=============================================================================
\* Modification History
\* Created Tue Oct 14 23:39:46 CEST 2025 by 20241799
