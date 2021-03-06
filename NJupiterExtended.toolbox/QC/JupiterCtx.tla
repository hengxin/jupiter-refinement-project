----------------------------- MODULE JupiterCtx -----------------------------
(*
Definitions for context-based Jupiter protocols, including AbsJupiter, CJupiter, and XJupiter.
*)
EXTENDS JupiterInterface, OT
-----------------------------------------------------------------------------
VARIABLES
    cseq,  \* cseq[c]: local sequence number at client c \in Client
    ds     \* ds[r]: document state (i.e., a set of Oids) of replica r \in Replica

ctxVars == <<cseq, ds>>
-----------------------------------------------------------------------------
Oid == [c: Client, seq: Nat]  \* operation identifier
Cop == [op: Op \cup {Nop}, oid: Oid, ctx: SUBSET Oid] \* context-based op

ClientOf(cop) == cop.oid.c

COT(lcop, rcop) == \* OT of lcop \in Cop against rcop \in Cop
    [lcop EXCEPT !.op = OT(lcop.op, rcop.op), !.ctx = @ \cup {rcop.oid}]

UpdateDS(r, oid) == \* update ds[r] to include new oid \in Oid
    ds' = [ds EXCEPT ![r] = @ \cup {oid}]
-----------------------------------------------------------------------------
TypeOKCtx ==
    /\ cseq \in [Client -> Nat]
    /\ ds \in [Replica -> SUBSET Oid]

InitCtx ==
    /\ cseq = [c \in Client |-> 1]
    /\ ds = [r \in Replica |-> {}]
    
DoCtx(c) ==
    /\ cseq' = [cseq EXCEPT ![c] = @ + 1]
    /\ UpdateDS(c, [c |-> c, seq |-> cseq[c]])  \* oid for newly generated operation

RevCtx(c) ==
    /\ UNCHANGED cseq
    /\ UpdateDS(c, Head(cincoming[c]).oid)
    
SRevCtx ==
    /\ UNCHANGED cseq
    /\ UpdateDS(Server, Head(sincoming).oid)
-----------------------------------------------------------------------------    
ClientConstraint == \* Each client generates at most 2 operations. 
    \forall c \in Client: cseq[c] <= 3
=============================================================================
\* Modification History
\* Last modified Tue Jan 29 10:11:36 CST 2019 by hengxin
\* Created Wed Dec 05 20:03:50 CST 2018 by hengxin