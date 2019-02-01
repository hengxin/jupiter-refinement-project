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
const_154899757151435000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154899757151436000 == 
{a, b}
----

\* SYMMETRY definition
symm_154899757151437000 == 
Permutations(const_154899757151436000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154899757151438000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154899757151439000 == 
Cop
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_154899757151441000 ==
\A cl \in Client: cseq[cl] <= 4
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154899757151442000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154899757151443000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Fri Feb 01 13:06:11 CST 2019 by hengxin
