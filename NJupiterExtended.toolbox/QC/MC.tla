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
const_155583127430382000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_155583127430483000 == 
{a, b}
----

\* SYMMETRY definition
symm_155583127430484000 == 
Permutations(const_155583127430483000)
----

\* CONSTANT definitions @modelParameterConstants:0Msg
const_155583127430485000 == 
NMsgEx
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_155583127430486000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_155583127430488000 ==
SpecEx
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_155583127430489000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sun Apr 21 15:21:14 CST 2019 by tangruize
