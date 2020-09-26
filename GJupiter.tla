------------------------------ MODULE GJupiter ------------------------------
(*************************** Google OT algorithm ***************************)
(* class Msg                                                               *)
(* // type: Client -> Server: [op, ack]  client generated op and acked num *)
(* //       Server -> Client: "ACKED"    last msg is acked                 *)
(* //                         op         generated by other clients        *)
(*                                                                         *)
(* class Client                                                            *)
(*     var outgoing // local generated operation buf: [op, stage]          *)
(*     var ack      // init to 0                                           *)
(*                                                                         *)
(*     synchronized procedure Do(op):                                      *)
(*         Apply(op)                                                       *)
(*         Append(outgoing, [op, "READY"])                                 *)
(*         Deliver()                                                       *)
(*                                                                         *)
(*     synchronized procedure Recv(msg):                                   *)
(*         ack := ack + 1                                                  *)
(*         if msg = "ACKED"                                                *)
(*             Remove(outgoing, 1)                                         *)
(*             Deliver()                                                   *)
(*         else                                                            *)
(*             xop, outgoing := Xform(msg, outgoing)                       *)
(*             Apply(xop)                                                  *)
(*                                                                         *)
(*     procedure Deliver():                                                *)
(*         if not Empty(outgoing) and outgoing[1].stage = "READY"          *)
(*             Send(Server, [outgoing[1], ack])                            *)
(*             outgoing[1].stage := "SENT"                                 *)
(*                                                                         *)
(* class Server     // single server                                       *)
(*     var outgoing // ops cannot be removed                               *)
(*                                                                         *)
(*     procedure SRecv(msg):                                               *)
(*         xop, xops := Xform(msg.op, outgoing[msg.ack+1:Len(outgoing)])   *)
(*         outgoing := outgoing[1:msg.ack] + xops + [xop]                  *)
(*         Send(msg's sender, "ACKED")                                     *)
(*         Send(other clients, xop)                                        *)
(***************************************************************************)

EXTENDS JupiterInterface, OT, BufferStateSpace

-----------------------------------------------------------------------------
VARIABLES
    outgoing, \* outgoing[r]: ops generated client or received by server.
    stage,    \* stage[c]: client msg sending stage.
    ack       \* ack[c]: client acked msg number. 

CONSTANTS READY, SENT, ACKED

Stages == {READY, SENT}

vars == <<intVars, outgoing, stage, ack>>

GMsg == \* messages exchanged by server and clients.
    [c: Client, op: Op \cup {Nop}, ack: Nat] \cup {ACKED} \cup Op \cup {Nop}

-----------------------------------------------------------------------------
TypeOK == 
    /\ TypeOKInt
    /\ outgoing \in [Replica -> Seq(Op \cup {Nop})]
    /\ stage \in [Client -> Seq(Stages)]
    /\ ack \in [Client -> Nat]

-----------------------------------------------------------------------------
Init == 
    /\ InitInt
    /\ outgoing = [r \in Replica |-> <<>>]
    /\ stage = [c \in Client |-> <<>>]
    /\ ack = [c \in Client |-> 0]

-----------------------------------------------------------------------------
Send(c) == 
    IF Len(stage[c]) # 0
    THEN /\ stage[c][1] = READY
         /\ stage' = [stage EXCEPT ![c] = <<SENT>> \o Tail(@)]
         /\ Comm!CSend([c |-> c, op |-> outgoing[c][1], ack |-> ack[c]])
         /\ UNCHANGED <<ack, aop, chins, outgoing, state>>
    ELSE FALSE

ClientPerform(c, m) ==
    IF m = ACKED \* last msg acked by server.
    THEN /\ outgoing' = [outgoing EXCEPT ![c] = Tail(@)]
         /\ stage' = [stage EXCEPT ![c] = Tail(@)]
         /\ SetNewAop(c, Nop) \* a dummy operation.
    ELSE \* op generated by other clients.
        LET xform == xFormFull(OT, m, outgoing[c])
        IN  /\ outgoing' = [outgoing EXCEPT ![c] = xform.xops]
            /\ UNCHANGED stage
            /\ SetNewAop(c, xform.xop)

ServerPerform(m) ==
    LET xform == xFormAppend(OT, m.op, outgoing[Server], m.ack)
    IN  /\ outgoing' = [outgoing EXCEPT ![Server] = xform.xops]
        /\ SetNewAop(Server, xform.xop)
        /\ Comm!SSendSameAck(m.c, ACKED, xform.xop)
        /\ UNCHANGED <<ack, stage>>

-----------------------------------------------------------------------------
DoOp(c, op) == 
    /\ SetNewAop(c, op)
    /\ outgoing' = [outgoing EXCEPT ![c] = Append(@, op)]
    /\ stage' = [stage EXCEPT ![c] = Append(@, READY)]
    /\ UNCHANGED <<ack, cincoming, sincoming>> \* DoOp will not send a msg.

-----------------------------------------------------------------------------
Do(c) == DoInt(DoOp, c)

Rev(c) == 
    /\ ack' = [ack EXCEPT ![c] = @ + 1]
    /\ RevInt(ClientPerform, c)

SRev == SRevInt(ServerPerform)

-----------------------------------------------------------------------------
Next == 
    \/ \E c \in Client: Do(c) \/ Rev(c) \/ Send(c)
    \/ SRev

Fairness == WF_vars(SRev \/ \E c \in Client: Rev(c))
    
Spec == Init /\ [][Next]_vars \* /\ Fairness

-----------------------------------------------------------------------------
EmptyOutgoing == \* all clients' outgoing is empty.
    \A c \in Client: Len(stage[c]) = 0

QC == \* Quiescent Consistency 
    EmptyOutgoing /\ Comm!EmptyChannel => Cardinality(Range(state)) = 1

THEOREM Spec => []QC

=============================================================================
\* Modification History
\* Last modified Sat Apr 20 22:49:46 CST 2019 by tangruize
\* Created Fri Mar 15 08:15:22 CST 2019 by tangruize