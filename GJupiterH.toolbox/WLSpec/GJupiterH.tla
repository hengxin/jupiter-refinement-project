----------------------------- MODULE GJupiterH ------------------------------
EXTENDS GJupiter
-----------------------------------------------------------------------------
VARIABLE list
varsH == <<vars, list>>

TypeOKH == TypeOK /\ (list \subseteq List)
-----------------------------------------------------------------------------
InitH == Init /\ list = {InitState}

DoH(c) == Do(c) /\ list' = list \cup {state'[c]}

RevH(c) == Rev(c) /\ list' = list \cup {state'[c]}

SendH(c) == Send(c) /\ UNCHANGED list

SRevH == SRev /\ list' = list \cup {state'[Server]}
-----------------------------------------------------------------------------
NextH == 
    \/ \E c \in Client: DoH(c) \/ RevH(c) \/ SendH(c)
    \/ SRevH

FairnessH ==
    WF_varsH(SRevH \/ \E c \in Client: RevH(c))    

SpecH == InitH /\ [][NextH]_varsH \* /\ FairnessH
-----------------------------------------------------------------------------
WLSpec == \* The weak list specification
    \A l1, l2 \in list: 
        /\ Injective(l1) 
        /\ Injective(l2) 
        /\ Compatible(l1, l2)

THEOREM SpecH => []WLSpec

=============================================================================
\* Modification History
\* Last modified Sat Apr 20 22:50:27 CST 2019 by tangruize
\* Created Fri Mar 15 11:00:49 CST 2019 by tangruize
