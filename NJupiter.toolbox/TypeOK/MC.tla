---- MODULE MC ----
EXTENDS NJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1555832794261373000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1555832794261374000 == 
{a, b}
----

\* SYMMETRY definition
symm_1555832794261375000 == 
Permutations(const_1555832794261374000)
----

\* CONSTANT definitions @modelParameterConstants:2Msg
const_1555832794261376000 == 
NMsg
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_1555832794261377000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1555832794261379000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1555832794261380000 ==
TypeOK
----
=============================================================================
\* Modification History
\* Created Sun Apr 21 15:46:34 CST 2019 by tangruize
