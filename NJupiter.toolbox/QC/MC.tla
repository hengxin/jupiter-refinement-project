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
const_1555833358700405000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_1555833358700406000 == 
{a, b}
----

\* SYMMETRY definition
symm_1555833358700407000 == 
Permutations(const_1555833358700406000)
----

\* CONSTANT definitions @modelParameterConstants:2Msg
const_1555833358700408000 == 
NMsg
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_1555833358700409000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1555833358700411000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1555833358700412000 ==
QC
----
=============================================================================
\* Modification History
\* Created Sun Apr 21 15:55:58 CST 2019 by tangruize
