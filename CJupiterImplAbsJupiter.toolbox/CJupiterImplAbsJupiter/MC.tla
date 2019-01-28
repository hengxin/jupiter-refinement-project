---- MODULE MC ----
EXTENDS CJupiterImplAbsJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_154815565259626000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_154815565259627000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_154815565259628000 == 
Permutations(const_154815565259626000)
----

\* CONSTANT definitions @modelParameterConstants:1InitState
const_154815565259629000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154815565259630000 == 
Cop
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_154815565259631000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154815565259632000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154815565259633000 ==
AbsJ!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jan 22 19:14:12 CST 2019 by hengxin
