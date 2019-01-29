---- MODULE MC ----
EXTENDS AbsJupiterH, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b, c
----

\* MV CONSTANT definitions Client
const_154868240754720000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Char
const_154868240754721000 == 
{a, b, c}
----

\* SYMMETRY definition
symm_154868240754722000 == 
Permutations(const_154868240754721000)
----

\* CONSTANT definitions @modelParameterConstants:2InitState
const_154868240754723000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4Msg
const_154868240754724000 == 
Cop
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_154868240754726000 ==
\A cl \in Client: cseq[cl] <= 4
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154868240754727000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154868240754728000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Mon Jan 28 21:33:27 CST 2019 by hengxin
