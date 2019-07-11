---- MODULE MC ----
EXTENDS NJupiterImplXJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT definitions Char
const_1555833145964397000 == 
{a, b}
----

\* MV CONSTANT definitions Client
const_1555833145965398000 == 
{c1, c2}
----

\* SYMMETRY definition
symm_1555833145965399000 == 
Permutations(const_1555833145964397000)
----

\* CONSTANT definitions @modelParameterConstants:1Msg
const_1555833145965400000 == 
NMsgEx
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_1555833145965401000 == 
<<>>
----

\* CONSTANT definition @modelParameterDefinitions:0
CONSTANT def_ov_1555833145965402000
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1555833145965403000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1555833145965404000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Sun Apr 21 15:52:25 CST 2019 by tangruize
