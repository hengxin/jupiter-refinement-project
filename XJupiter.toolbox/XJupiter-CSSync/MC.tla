---- MODULE MC ----
EXTENDS XJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_15415689804879000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154156898048710000 == 
{a, b}
----

\* SYMMETRY definition
symm_154156898048711000 == 
Permutations(const_15415689804879000) \union Permutations(const_154156898048710000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154156898048712000 == 
<<>>
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154156898048714000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154156898048715000 ==
CSSync
----
=============================================================================
\* Modification History
\* Created Wed Nov 07 13:36:20 CST 2018 by hengxin
