---- MODULE MC ----
EXTENDS AbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154641066505116000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154641066505117000 == 
{a, b}
----

\* SYMMETRY definition
symm_154641066505118000 == 
Permutations(const_154641066505117000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154641066505119000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154641066505121000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154641066505122000 ==
Compactness
----
=============================================================================
\* Modification History
\* Created Wed Jan 02 14:31:05 CST 2019 by hengxin
