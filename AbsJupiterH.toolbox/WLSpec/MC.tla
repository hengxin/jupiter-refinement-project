---- MODULE MC ----
EXTENDS AbsJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154814339330918000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154814339330919000 == 
{a, b}
----

\* SYMMETRY definition
symm_154814339330920000 == 
Permutations(const_154814339330919000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154814339330921000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154814339330922000 == 
Cop
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154814339330924000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154814339330925000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Tue Jan 22 15:49:53 CST 2019 by hengxin
