---- MODULE MC ----
EXTENDS NJupiterExtended, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1555832697613357000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1555832697613358000 == 
{a, b}
----

\* SYMMETRY definition
symm_1555832697613359000 == 
Permutations(const_1555832697613358000)
----

\* CONSTANT definitions @modelParameterConstants:0Msg
const_1555832697613360000 == 
NMsgEx
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_1555832697613361000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1555832697613363000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1555832697613364000 ==
TypeOKEx
----
=============================================================================
\* Modification History
\* Created Sun Apr 21 15:44:57 CST 2019 by tangruize
