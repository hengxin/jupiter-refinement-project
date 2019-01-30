---- MODULE MC ----
EXTENDS AJupiterImplXJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154874507885410000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154874507885411000 == 
{a, b}
----

\* SYMMETRY definition
symm_154874507885412000 == 
Permutations(const_154874507885411000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154874507885413000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154874507885414000 == 
AJMsgEx
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154874507885416000 ==
SpecImpl
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154874507885417000 ==
XJ!Spec
----
=============================================================================
\* Modification History
\* Created Tue Jan 29 14:57:58 CST 2019 by hengxin
