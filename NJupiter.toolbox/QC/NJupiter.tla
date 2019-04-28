----------------------------- MODULE NJupiter -------------------------------
(*********************** Original Jupiter algorithm ************************)
(* class Msg                                                               *)
(* // type: [op, seq]                                                      *)
(*                                                                         *)
(* class Client                                                            *)
(*     var lseq     // local generated msg number, init to 0               *)
(*     var gseq     // global received msg number, init to 0               *)
(*     var outgoing // [op, seq]                                           *)
(*                                                                         *)
(*     synchronized procedure Do(op):                                      *)
(*         Apply(op)                                                       *)
(*         Send(the other side, [op, gseq])                                *)
(*         Append(outgoing, [op, lseq])                                    *)
(*         lseq := lseq + 1                                                *)
(*                                                                         *)
(*     synchronized procedure Recv(msg):                                   *)
(*         RemoveIf(outgoing, lambda i: i.seq < msg.seq)                   *)
(*         xop, outgoing := Xform(msg.op, outgoing)                        *)
(*         Apply(xop)                                                      *)
(*         gseq := gseq + 1                                                *)
(*                                                                         *)
(* class ServerThread // every client has a corresponding server thread    *)
(*     var lseq // in fact, its meaning is gseq in server's scenario       *)
(*              // for reusing Client funcs, I don't exchange their usages *)
(*     var gseq                                                            *)
(*     var outgoing                                                        *)
(*                                                                         *)
(*     synchronized procedure SRecv(msg):                                  *)
(*         Client.Recv(msg)  // just reuse the code                        *)
(*         SignalOtherServerThreads(xop)                                   *)
(*                                                                         *)
(*     synchronized procedure Signaled(op):                                *)
(*         Client.Do(op)     // just reuse the code                        *)
(***************************************************************************)

EXTENDS JupiterInterface, OT, BufferStateSpace
-----------------------------------------------------------------------------
VARIABLES
    cbuf,  \* cbuf[c]: client outgoing: [op, seq]
    cseq,  \* cseq[c]: client lseq gseq: [l, g]
    sbuf,
    sseq

vars == <<intVars, cbuf, cseq, sbuf, sseq>>

NMsg == 
    [c: Client, seq: Nat, op: Op \cup {Nop}] \cup \* client -> server
    [seq: Nat, op: Op \cup {Nop}] \* server -> client
-----------------------------------------------------------------------------
TypeOK == 
    /\ TypeOKInt
    /\ cbuf \in [Client -> Seq([op: Op \cup {Nop}, seq: Nat])]
    /\ cseq \in [Client -> [l: Nat, g: Nat]]
    /\ cbuf \in [Client -> Seq([op: Op \cup {Nop}, seq: Nat])]
    /\ cseq \in [Client -> [l: Nat, g: Nat]]
-----------------------------------------------------------------------------
Init == 
    /\ InitInt
    /\ cbuf = [c \in Client |-> <<>>]
    /\ cseq = [c \in Client |-> [l |-> 0, g |-> 0]]
    /\ sbuf = [c \in Client |-> <<>>]
    /\ sseq = [c \in Client |-> [l |-> 0, g |-> 0]]
-----------------------------------------------------------------------------
RemoveAckedOps(s, seq) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0
        THEN << >>
        ELSE IF s[i].seq >= seq
             THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]

OTWrapper(l, r) == [op |-> OT(l.op, r.op), seq |-> l.seq]

ClientPerform(c, m) == 
    LET xform == xFormFull(OTWrapper, m, RemoveAckedOps(cbuf[c], m.seq))
    IN  /\ cbuf' = [cbuf EXCEPT ![c] = xform.xops]
        /\ cseq' = [cseq EXCEPT ![c] = [l |-> @.l, g |-> @.g + 1]]
        /\ SetNewAop(c, xform.xop.op)

ServerPerform(m) == 
    LET c == m.c
        xform == xFormFull(OTWrapper, m, RemoveAckedOps(sbuf[c], m.seq))
        xop == xform.xop.op
    IN  /\ sseq' = [cl \in Client |-> IF cl = c
                                      THEN [l |-> sseq[cl].l + 1, g |-> sseq[cl].g]
                                      ELSE [l |-> sseq[cl].l, g |-> sseq[cl].g + 1]]
        /\ sbuf' = [cl \in Client |-> IF cl = c
                                      THEN xform.xops 
                                      ELSE Append(sbuf[cl], [op |-> xop, seq |-> sseq[cl].g])]
        /\ SetNewAop(Server, xop)
        /\ Comm!SSend(c, [cl \in Client |-> [seq |-> sseq[cl].l, op |-> xop]])
-----------------------------------------------------------------------------
DoOp(c, op) == 
    /\ SetNewAop(c, op)
    /\ cbuf' = [cbuf EXCEPT ![c] = Append(@, [op |-> op, seq |-> cseq[c].l])]
    /\ cseq' = [cseq EXCEPT ![c] = [l |-> @.l + 1, g |-> @.g]]
    /\ Comm!CSend([c |-> c, seq |-> cseq[c].g, op |-> op])

Do(c) == 
    /\ DoInt(DoOp, c)
    /\ UNCHANGED <<sbuf, sseq>>

Rev(c) == 
    /\ RevInt(ClientPerform, c)
    /\ UNCHANGED <<sbuf, sseq>>

SRev == 
    /\ SRevInt(ServerPerform)
    /\ UNCHANGED <<cbuf, cseq>>
-----------------------------------------------------------------------------
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c)
    \/ SRev

Fairness == 
    WF_vars(SRev \/ \E c \in Client: Rev(c))
    
Spec == Init /\ [][Next]_vars \* /\ Fairness
-----------------------------------------------------------------------------
QC == \* Quiescent Consistency 
    Comm!EmptyChannel => Cardinality(Range(state)) = 1

THEOREM Spec => []QC
=============================================================================
\* Modification History
\* Last modified Sun Apr 21 09:37:06 CST 2019 by tangruize
\* Last modified Thu Jan 17 10:30:39 CST 2019 by hengxin
\* Created Satchins,  Jun 23 17:14:18 CST 2018 by hengxin