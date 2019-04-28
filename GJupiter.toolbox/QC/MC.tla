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
const_1555833386926413000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1555833386926414000 == 
{a, b}
----

\* SYMMETRY definition
symm_1555833386926415000 == 
Permutations(const_1555833386926414000)
----

\* CONSTANT definitions @modelParameterConstants:5Msg
const_1555833386926416000 == 
GMsg
----

\* CONSTANT definitions @modelParameterConstants:6InitState
const_1555833386926417000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1555833386926419000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1555833386926420000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sun Apr 21 15:56:26 CST 2019 by tangruize
