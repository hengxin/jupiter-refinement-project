----------------------------- MODULE JupiterOid -----------------------------
EXTENDS JupiterInterface, OT
-----------------------------------------------------------------------------
VARIABLES
    cseq    \* cseq[c]: local sequence number at client c \in Client

oidVars== <<cseq>>
-----------------------------------------------------------------------------
Oid == [c: Client, seq: Nat]  \* operation identifier

Oop == [op: Op \cup {Nop}, oid: Oid] \* operation identified by oid

OOT(loop, roop) == \* OT of loop \in Oop against roop \in Oop
    [loop EXCEPT !.op = OT(loop.op, roop.op)]
    
xForm(r, cop) == \* Transform $cop$ at replica $r$.
    LET ctxDiff == ds[r] \ cop.ctx \* calculate concurrent operations
        xFormHelper(coph, ctxDiffh, xcopssh) == \* Return transformed $xcop$ and
            IF ctxDiffh = {} THEN [xcop |-> coph, xcopss |-> xcopssh] \* new $copss$ 
            ELSE LET foidh == CHOOSE oid \in ctxDiffh: \* the first $oid$ in $ctxDiffh$ 
                                \A id \in ctxDiffh \ {oid}: tb(oid, id, serial[r]) 
                     fcoph == CHOOSE fcop \in copss[r]: 
                                fcop.oid = foidh /\ fcop.ctx = coph.ctx \* CC
                     xcoph == COT(coph, fcoph)
                    xfcoph == COT(fcoph, coph)
                 IN  xFormHelper(xcoph, ctxDiffh \ {fcoph.oid}, 
                                        xcopssh \cup {xcoph, xfcoph})
    IN  xFormHelper(cop, ctxDiff, copss[r] \cup {cop}) 
=============================================================================
\* Modification History
\* Last modified Thu Apr 04 10:47:57 CST 2019 by hengxin
\* Created Mon Feb 25 21:32:56 CST 2019 by hengxin