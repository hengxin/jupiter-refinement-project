---- MODULE MC ----
EXTENDS AbsJupiterH2, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a, b
----

\* MV CONSTANT definitions Client
const_154631124155631000 == 
{c1, c2}
----

\* MV CONSTANT definitions Char
const_154631124155632000 == 
{a, b}
----

\* SYMMETRY definition
symm_154631124155633000 == 
Permutations(const_154631124155632000)
----

\* CONSTANT definitions @modelParameterConstants:0Msg
const_154631124155634000 == 
Cop
----

\* CONSTANT definitions @modelParameterConstants:3InitState
const_154631124155635000 == 
<<>>
----

\* CONSTANT definitions @modelParameterConstants:4SRevImpl
const_154631124155636000 == 
SRev
----

\* CONSTANT definitions @modelParameterConstants:5Vars
const_154631124155637000 == 
vars
----

\* CONSTANT definitions @modelParameterConstants:7InitImpl
const_154631124155638000 == 
Init
----

\* CONSTANT definitions @modelParameterConstants:8TypeOKImpl
const_154631124155639000 == 
TypeOK
----

\* CONSTANT definitions @modelParameterConstants:9NextImpl
const_154631124155640000 == 
Next
----

\* CONSTANT definitions @modelParameterConstants:10RevImpl(c)
const_154631124155641000(c) == 
Rev(c)
----

\* CONSTANT definitions @modelParameterConstants:11DoImpl(c)
const_154631124155642000(c) == 
Do(c)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154631124155644000 ==
SpecH
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154631124155645000 ==
WLSpec
----
=============================================================================
\* Modification History
\* Created Tue Jan 01 10:54:01 CST 2019 by hengxin
