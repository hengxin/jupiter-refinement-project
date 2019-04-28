------------------------ MODULE NJupiterImplXJupiter ------------------------
EXTENDS NJupiterExtended, GraphStateSpace
-----------------------------------------------------------------------------
VARIABLES c2ss, s2ss

varsImpl == <<varsEx, c2ss, s2ss>>
-----------------------------------------------------------------------------
TypeOKImpl ==
    /\ TypeOKEx
    /\ \A c \in Client: IsSS(c2ss[c]) /\ IsSS(s2ss[c])

InitImpl ==
    /\ InitEx
    /\ c2ss = [c \in Client |-> EmptySS]    
    /\ s2ss = [c \in Client |-> EmptySS]    
-----------------------------------------------------------------------------
DoOpImpl(c, op) == 
    /\ DoOpEx(c, op)
    /\ LET cop == [op |-> op, oid |-> [c |-> c, seq |-> cseq[c]], ctx |-> ds[c]] 
       IN  c2ss' = [c2ss EXCEPT ![c] = 
                        @ (+) [node |-> {ds'[c]},
                               edge |-> {[from |-> ds[c], to |-> ds'[c], cop |-> cop]}]]
    /\ UNCHANGED s2ss

ClientPerformImpl(c, m) ==
    /\ LET xform == xFormCopCops(m.cop, RemoveAckedOps(cbuf[c], m.ack)) \* [xcop, xss, lss]
       IN  c2ss' = [c2ss EXCEPT ![c] = @ (+) xform.xss]
    /\ UNCHANGED s2ss

ServerPerformImpl(m) ==
    /\ LET c == ClientOf(m.cop)
           xform == xFormCopCops(m.cop, RemoveAckedOps(sbuf[c], m.ack)) \* [xcop, xss, lss]
       IN  s2ss' = [cl \in Client |-> IF cl = c THEN s2ss[cl] (+) xform.xss 
                                                ELSE s2ss[cl] (+) xform.lss]
    /\ UNCHANGED c2ss
-----------------------------------------------------------------------------
DoImpl(c) == 
    /\ DoCtx(c)
    /\ DoInt(DoOpImpl, c) \* TODO: refactor to use DoEx(c); cannot use two DoInt
    /\ UNCHANGED <<sbuf, sack>>

RevImpl(c) ==
    /\ RevEx(c)
    /\ RevInt(ClientPerformImpl, c)

SRevImpl ==
    /\ SRevEx
    /\ SRevInt(ServerPerformImpl)
-----------------------------------------------------------------------------
NextImpl ==
    \/ \E c \in Client: DoImpl(c) \/ RevImpl(c)
    \/ SRevImpl
    
FairnessImpl == 
    WF_varsImpl(SRevImpl \/ \E c \in Client: RevImpl(c)) 

SpecImpl == InitImpl /\ [][NextImpl]_varsImpl \* /\ FairnessImpl
-----------------------------------------------------------------------------
XJ == INSTANCE XJupiter WITH Msg <- Cop,
            cincoming <- cincomingXJ, sincoming <- sincomingXJ

THEOREM SpecImpl => XJ!Spec
=============================================================================
\* Modification History
\* Last modified Sun Apr 21 15:52:19 CST 2019 by tangruize
\* Created Wed Mar 20 05:24:46 CST 2019 by tangruize
