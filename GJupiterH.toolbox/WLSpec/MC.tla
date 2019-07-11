---- MODULE MC ----
EXTENDS GJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_155577183236666000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_155577183236667000 == 
{a, b}
----

\* SYMMETRY definition
symm_155577183236668000 == 
Permutations(const_155577183236667000)
----

\* CONSTANT definitions @modelParameterConstants:0Msg
const_155577183236669000 == 
GMsg
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_155577183236670000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_155577183236772000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_155577183236773000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Sat Apr 20 22:50:32 CST 2019 by tangruize
