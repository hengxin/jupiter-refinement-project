---- MODULE MC ----
EXTENDS AJupiter, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154822459801834000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154822459801935000 == 
{a, b}
----

\* SYMMETRY definition
symm_154822459801936000 == 
Permutations(const_154822459801935000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154822459801937000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154822459801938000 == 
AJMsg
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154822459801940000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154822459801941000 ==
QC
----
=============================================================================
\* Modification History
\* Created Wed Jan 23 14:23:18 CST 2019 by hengxin
