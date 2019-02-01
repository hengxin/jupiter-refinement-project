---- MODULE MC ----
EXTENDS CJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154780303562087000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154780303562088000 == 
{a, b}
----

\* SYMMETRY definition
symm_154780303562089000 == 
Permutations(const_154780303562088000)
----

\* CONSTANT definitions @modelParameterConstants:0Msg
const_154780303562090000 == 
Cop
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_154780303562091000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154780303562093000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154780303562094000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Fri Jan 18 17:17:15 CST 2019 by hengxin
