-------------------------- MODULE NJupiterExtended --------------------------
(*
NJupiter extended with JupiterCtx. Used to show NJupiter implements XJupiter.
*)
EXTENDS JupiterCtx, BufferStateSpace
-----------------------------------------------------------------------------
VARIABLES cbuf, cack, sbuf, sack, cincomingXJ, sincomingXJ
    \* variable name cseq has been used in JupiterCtx, we use cack instead.

varsEx == <<intVars, ctxVars, cbuf, cack, sbuf, sack, cincomingXJ, sincomingXJ>>

NMsgEx == [ack: Nat, cop: Cop, oid: Oid] 
commXJ == INSTANCE CSComm WITH Msg <- Cop,
                               cincoming <- cincomingXJ,
                               sincoming <- sincomingXJ
-----------------------------------------------------------------------------
TypeOKEx == 
    /\ TypeOKInt
    /\ TypeOKCtx
    /\ commXJ!TypeOK
    /\ cack \in [Client -> [l: Nat, g: Nat]]
    /\ sack \in [Client -> [l: Nat, g: Nat]]
    /\ cbuf \in [Client -> Seq([cop: Cop, ack: Nat])]
    /\ sbuf \in [Client -> Seq([cop: Cop, ack: Nat])]
-----------------------------------------------------------------------------
InitEx == 
    /\ InitInt
    /\ InitCtx
    /\ commXJ!Init
    /\ cack = [c \in Client |-> [l |-> 0, g |-> 0]]
    /\ sack = [c \in Client |-> [l |-> 0, g |-> 0]]
    /\ cbuf = [c \in Client |-> <<>>]
    /\ sbuf = [c \in Client |-> <<>>]
-----------------------------------------------------------------------------
DoOpEx(c, op) == 
    LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cack[c].l + 1], ctx |-> ds[c]]
    IN /\ cack' = [cack EXCEPT ![c] = [l |-> @.l + 1, g |-> @.g]]
       /\ cbuf' = [cbuf EXCEPT ![c] = Append(@, [cop |-> cop, ack |-> cack[c].l])]
       /\ SetNewAop(c, op)
       /\ Comm!CSend([ack |-> cack[c].g, cop |-> cop, oid |-> cop.oid])
       /\ commXJ!CSend(cop)

RemoveAckedOps(s, ack) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0
        THEN << >>
        ELSE IF s[i].ack >= ack
             THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]

COTWrapper(l, r) == [cop |-> COT(l.cop, r.cop), ack |-> l.ack]

ClientPerformEx(c, m) == 
    LET xform == xFormFull(COTWrapper, m, RemoveAckedOps(cbuf[c], m.ack))
    IN  /\ cbuf' = [cbuf EXCEPT ![c] = xform.xops]
        /\ cack' = [cack EXCEPT ![c] = [l |-> @.l, g |-> @.g + 1]]
        /\ SetNewAop(c, xform.xop.cop.op)

ServerPerformEx(m) == 
    LET c == ClientOf(m.cop)
        xform == xFormFull(COTWrapper, m, RemoveAckedOps(sbuf[c], m.ack))
        xcop == xform.xop.cop
    IN  /\ sack' = [cl \in Client |-> IF cl = c
                                      THEN [l |-> sack[cl].l + 1, g |-> sack[cl].g]
                                      ELSE [l |-> sack[cl].l, g |-> sack[cl].g + 1]]
        /\ sbuf' = [cl \in Client |-> IF cl = c
                                      THEN xform.xops 
                                      ELSE Append(sbuf[cl], [cop |-> xcop, ack |-> sack[cl].g])]
        /\ SetNewAop(Server, xcop.op)
        /\ Comm!SSend(c, [cl \in Client |-> [ack |-> sack[cl].l,
                                             cop |-> xcop,
                                             oid |-> xcop.oid]])
        /\ commXJ!SSendSame(c, xcop)
-----------------------------------------------------------------------------
DoEx(c) == 
    /\ DoInt(DoOpEx, c)
    /\ DoCtx(c)
    /\ UNCHANGED <<sbuf, sack>>

RevEx(c) == 
    /\ RevInt(ClientPerformEx, c)
    /\ RevCtx(c)
    /\ commXJ!CRev(c)
    /\ UNCHANGED <<sbuf, sack>>

SRevEx == 
    /\ SRevInt(ServerPerformEx)
    /\ SRevCtx
    /\ commXJ!SRev
    /\ UNCHANGED <<cbuf, cack>>
-----------------------------------------------------------------------------
NextEx == 
    \/ \E c \in Client: DoEx(c) \/ RevEx(c)
    \/ SRevEx

FairnessEx == 
    WF_varsEx(SRevEx \/ \E c \in Client: RevEx(c))
    
SpecEx == InitEx /\ [][NextEx]_varsEx \* /\ FairnessEx
-----------------------------------------------------------------------------
QC == \* Quiescent Consistency 
    Comm!EmptyChannel => Cardinality(Range(state)) = 1

THEOREM SpecEx => []QC
=============================================================================
\* Modification History
\* Last modified Tue May 14 13:34:34 CST 2019 by tangruize
\* Created Wed Mar 19 04:49:31 CST 2019 by tangruize
