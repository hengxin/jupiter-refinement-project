---- MODULE MC ----
EXTENDS NJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_1555832878926389000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1555832878926390000 == 
{a, b}
----

\* SYMMETRY definition
symm_1555832878926391000 == 
Permutations(const_1555832878926390000)
----

\* CONSTANT definitions @modelParameterConstants:0Msg
const_1555832878926392000 == 
NMsg
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_1555832878926393000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1555832878927395000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1555832878927396000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sun Apr 21 15:47:58 CST 2019 by tangruize
