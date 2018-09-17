------------------------------ MODULE JupiterH ------------------------------
(*
Specification of Jupiter with a history variable "list",
upon which we define the weak list specification WLSpec.
*)

EXTENDS Jupiter, AdditionalSequenceOperators
-----------------------------------------------------------------------------
VARIABLES list
    
VarsH == <<Vars, list>>

TypeOKH == 
    /\ TypeOK
    /\ list \subseteq List
-----------------------------------------------------------------------------
InitH == 
    /\ Init 
    /\ list = {InitState}

DoH(c) == 
    /\ Do(c) 
    /\ list' = list \cup {state'[c]}

RevH(c) == 
    /\ Rev(c) 
    /\ list' = list \cup {state'[c]}

SRevH == 
    /\ SRev 
    /\ list' = list \cup {state'[Server]}
-------------------------------------------------------------
NextH == 
    \/ \E c \in Client: DoH(c) \/ RevH(c)
    \/ SRevH
    
SpecH == InitH /\ [][NextH]_VarsH /\ WF_VarsH(NextH)
-------------------------------------------------------------
(*********************************************************************)
(* Weak List Consistency (WLSpec)                                    *)
(*********************************************************************)
WLSpec == \A l1, l2 \in list: 
            /\ Injective(l1) 
            /\ Injective(l2) 
            /\ Compatible(l1, l2)

THEOREM SpecH => WLSpec
(*********************************************************************)
(* Strong List Consistency (SLSpec)                                  *)
(*********************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue Sep 11 20:55:59 CST 2018 by hengxin
\* Created Tue Sep 11 17:34:23 CST 2018 by hengxin
