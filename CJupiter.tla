------------------------------ MODULE CJupiter ------------------------------
(*
Specification of our own CJupiter protocol; see Wei@OPODIS'2018.
*)
EXTENDS JupiterSerial, GraphStateSpace 
-----------------------------------------------------------------------------
VARIABLES
    css    \* css[r]: the n-ary ordered state space at replica r \in Replica

vars == <<intVars, ctxVars, serialVars, css>>
-----------------------------------------------------------------------------
TypeOK == 
    /\ TypeOKInt
    /\ TypeOKCtx
    /\ TypeOKSerial
    /\ \A r \in Replica: IsSS(css[r])
-----------------------------------------------------------------------------
Init == 
    /\ InitInt
    /\ InitCtx
    /\ InitSerial
    /\ css = [r \in Replica |-> EmptySS]
-----------------------------------------------------------------------------
NextEdge(r, u, ss) == \* Return the first outgoing edge from u in ss at replica r
    CHOOSE e \in ss.edge: 
        /\e.from = u 
        /\\A ue \in ss.edge \ {e}: 
            (ue.from = u) => tb(e.cop.oid, ue.cop.oid, serial[r])
    
Perform(r, cop) == 
    LET xform == xForm(NextEdge, r, cop, css[r])  \* xform: [xcop, xss, lss]
    IN  /\ css' = [css EXCEPT ![r] = @ (+) xform.xss]
        /\ SetNewAop(r, xform.xcop.op)

ClientPerform(c, cop) == Perform(c, cop)

ServerPerform(cop) ==
    /\ Perform(Server, cop)
    /\ Comm!SSendSame(ClientOf(cop), cop)  \* broadcast the original cop 
-----------------------------------------------------------------------------
DoOp(c, op) == 
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq[c]], ctx |-> ds[c]]
     IN /\ ClientPerform(c, cop)
        /\ Comm!CSend(cop)

Do(c) == 
    /\ DoInt(DoOp, c) 
    /\ DoCtx(c)
    /\ DoSerial(c)

Rev(c) == 
    /\ RevInt(ClientPerform, c)
    /\ RevCtx(c)
    /\ RevSerial(c)

SRev == 
    /\ SRevInt(ServerPerform)
    /\ SRevCtx
    /\ SRevSerial
-----------------------------------------------------------------------------
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev

Fairness == 
    WF_vars(SRev \/ \E c \in Client: Rev(c))

Spec == Init /\ [][Next]_vars \* /\ Fairness
-----------------------------------------------------------------------------
Compactness == \* Compactness of CJupiter: the CSSes at all replicas are the same.
    Comm!EmptyChannel => Cardinality(Range(css)) = 1

THEOREM Spec => []Compactness
=============================================================================
\* Modification History
\* Last modified Mon Jan 28 20:08:29 CST 2019 by hengxin
\* Created Sat Sep 01 11:08:00 CST 2018 by hengxin