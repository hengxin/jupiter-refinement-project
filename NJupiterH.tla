----------------------------- MODULE NJupiterH ------------------------------
EXTENDS NJupiter
-----------------------------------------------------------------------------
VARIABLE list
varsH == <<vars, list>>

TypeOKH == TypeOK /\ (list \subseteq List)
-----------------------------------------------------------------------------
InitH == Init /\ list = {InitState}

DoH(c) == Do(c) /\ list' = list \cup {state'[c]}

RevH(c) == Rev(c) /\ list' = list \cup {state'[c]}

SRevH == SRev /\ list' = list \cup {state'[Server]}
-----------------------------------------------------------------------------
NextH == 
    \/ \E c \in Client: DoH(c) \/ RevH(c)
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
\* Last modified Thu Apr 18 11:25:09 CST 2019 by tangruize
\* Created Tue Mar 12 10:16:31 CST 2019 by tangruize
