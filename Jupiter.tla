------------------------------ MODULE Jupiter ------------------------------
(*
Specification of the interface of a family of Jupiter protocols,
which adopt the C/S architecture.
*)

EXTENDS Integers, Sequences, FiniteSets, AdditionalFunctionOperators
-----------------------------------------------------------------------------
CONSTANTS
    Client,     \* the set of client replicas
    Server,     \* the (unique) server replica
    Char,       \* set of characters allowed
    InitState,  \* the initial state of each replica
    TypeOK,
    Init,
    Do(_),
    Rev(_),
    SRev,
    Vars
    
Replica == Client \cup {Server}

List == Seq(Char \cup Range(InitState))   \* all possible lists/strings
MaxLen == Cardinality(Char) + Len(InitState) \* the max length of lists in any states;
    \* We assume that all inserted elements are unique.

ClientNum == Cardinality(Client)
Priority == CHOOSE f \in [Client -> 1 .. ClientNum] : Injective(f)
----------------------------------------------------------------------
ASSUME 
    /\ Range(InitState) \cap Char = {}
    /\ Priority \in [Client -> 1 .. ClientNum]
-----------------------------------------------------------------------------
(*********************************************************************)
(* The set of all operations.                                        *)
(* Note: The positions are indexed from 1. *)
(*********************************************************************)
Rd == [type: {"Rd"}]
Del == [type: {"Del"}, pos: 1 .. MaxLen]
Ins == [type: {"Ins"}, pos: 1 .. (MaxLen + 1), ch: Char, pr: 1 .. ClientNum] \* pr: priority

Op == Ins \cup Del  \* Now we don't consider Rd operations.
-----------------------------------------------------------------------------
VARIABLES
    state,      \* state[r]: state (the list content) of replica r \in Replica
    (*
       For communication between the Server and the Clients:
    *)
    cincoming,  \* cincoming[c]: incoming channel at the client c \in Client
    sincoming   \* sincoming: incoming channel at the Server
=============================================================================
\* Modification History
\* Last modified Tue Sep 11 21:03:34 CST 2018 by hengxin
\* Created Tue Sep 11 17:35:14 CST 2018 by hengxin