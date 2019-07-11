---- MODULE MC ----
EXTENDS GJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1555668027790266000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1555668027790267000 == 
{a, b}
----

\* SYMMETRY definition
symm_1555668027790268000 == 
Permutations(const_1555668027790267000)
----

\* CONSTANT definitions @modelParameterConstants:5Msg
const_1555668027790269000 == 
GMsg
----

\* CONSTANT definitions @modelParameterConstants:6InitState
const_1555668027790270000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1555668027790272000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1555668027790273000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Fri Apr 19 18:00:27 CST 2019 by tangruize
