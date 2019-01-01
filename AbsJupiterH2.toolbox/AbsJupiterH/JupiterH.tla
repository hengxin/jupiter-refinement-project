------------------------------ MODULE JupiterH ------------------------------
(*
Jupiter with a history variable (i.e., list) collecting all list states across the system.
*)
EXTENDS JupiterInterface
-------------------------------------------------------------
CONSTANTS
    TypeOKImpl,
    InitImpl, NextImpl,
    DoImpl(_), RevImpl(_), SRevImpl,
    Msg,
    Vars
-------------------------------------------------------------
VARIABLES list
varsH == <<Vars, list>>
-------------------------------------------------------------
TypeOKH == 
    /\ TypeOKImpl 
    /\ (list \subseteq List)

InitH == 
    /\ InitImpl 
    /\ list = {InitState}

DoH(c) == 
    /\ DoImpl(c) 
    /\ list' = list \cup {state'[c]}

RevH(c) == 
    /\ RevImpl(c) 
    /\ list' = list \cup {state'[c]}

SRevH == 
    /\ SRevImpl 
    /\ list' = list \cup {state'[Server]}
-------------------------------------------------------------
NextH == 
    \/ \E c \in Client: DoH(c) \/ RevH(c)
    \/ SRevH

FairnessH ==
    WF_varsH(SRevH \/ \E c \in Client: RevH(c))    

SpecH == InitH /\ [][NextH]_varsH \* /\ FairnessH
-------------------------------------------------------------
WLSpec == \* The weak list specification
    Comm(Msg)!EmptyChannel 
        => \A l1, l2 \in list: 
            /\ Injective(l1) 
            /\ Injective(l2) 
            /\ Compatible(l1, l2)

THEOREM SpecH => WLSpec
=============================================================================
\* Modification History
\* Last modified Tue Jan 01 10:48:21 CST 2019 by hengxin
\* Created Tue Jan 01 09:56:25 CST 2019 by hengxin