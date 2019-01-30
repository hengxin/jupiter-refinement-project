----------------------------- MODULE AJupiterH -----------------------------
EXTENDS AJupiter
-------------------------------------------------------------
VARIABLE list
varsH == <<vars, list>>

TypeOKH == TypeOK /\ (list \subseteq List)
-------------------------------------------------------------
InitH == Init /\ list = {InitState}

DoH(c) == Do(c) /\ list' = list \cup {state'[c]}

RevH(c) == Rev(c) /\ list' = list \cup {state'[c]}

SRevH == SRev /\ list' = list \cup {state'[Server]}
-------------------------------------------------------------
NextH == 
    \/ \E c \in Client: DoH(c) \/ RevH(c)
    \/ SRevH

FairnessH ==
    WF_varsH(SRevH \/ \E c \in Client: RevH(c))    

SpecH == InitH /\ [][NextH]_varsH \* /\ FairnessH
-------------------------------------------------------------
WLSpec == \* The weak list specification
    Comm!EmptyChannel   \* no need to check Compatible at every state 
        => \A l1, l2 \in list: 
            /\ Injective(l1) \* no duplicate elements
            /\ Injective(l2) \* true due to our distinctness assumption
            /\ Compatible(l1, l2)

THEOREM SpecH => []WLSpec
=============================================================================
\* Modification History
\* Last modified Wed Jan 30 21:37:29 CST 2019 by hengxin
\* Created Thu Aug 30 21:26:18 CST 2018 by hengxin