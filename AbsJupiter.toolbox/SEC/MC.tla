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
const_15486772221102000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_15486772221103000 == 
{a, b}
----

\* SYMMETRY definition
symm_15486772221104000 == 
Permutations(const_15486772221103000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_15486772221105000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_15486772221106000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15486772221118000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15486772221119000 ==
SEC
----
=============================================================================
\* Modification History
\* Created Mon Jan 28 20:07:02 CST 2019 by hengxin
