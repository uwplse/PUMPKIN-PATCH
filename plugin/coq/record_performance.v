From Coq Require Import Vectors.Vector.

Require Import Patcher.Patch.

(*
 * This module shows how you can use DEVOID with the Replace Convertible command
 * in order to optimize lifting. Here we replace large constants like 32 and 128.
 * It also shows all three plugins together in action.
 *)

Set DEVOID search prove equivalence.
Set DEVOID lift type.

Module CryptolPrimitives.

  Definition seq (n : nat) (T : Type) := Vector.t T n.

  Axiom ecAt : forall (n : nat), forall (a : Type), forall (i : nat), (((@CryptolPrimitives.seq) (n) (a))) -> (((@CryptolPrimitives.seq) (i) (@bool))) -> a.

End CryptolPrimitives.

Definition TCNum (n : nat) := n.

Definition seq := CryptolPrimitives.seq.

Module Handshake.

  (** [cry_handshake] is the [handshake] type as it comes out of the translation
from Cryptol to Coq.  The fields have been inlined into a nested tuple type.

This is what the original [handshake] type looked like:

type handshake = {handshake_type : [32]
                 ,message_number : [32]
                 }
   *)
  Definition handshake : Type := (seq 32 bool * seq 32 bool).

  (** We can define more convenient types for [handshake] and [connection] in Coq.
Ideally, we'd like the translation to generate those, but in its current state,
it goes through an intermediate language that does not support records and
record types.
   *)
  Record Handshake :=
    MkHandshake
      {
        handshakeType : seq 32 bool;
        messageNumber : seq 32 bool;
      }.

  Scheme Induction for Handshake Sort Prop.
  Scheme Induction for Handshake Sort Type.
  Scheme Induction for Handshake Sort Set.

  Definition get_handshake_type (h : handshake) : seq 32 bool :=
    fst h.

  Definition get_message_number (h : handshake) : seq 32 bool :=
    snd h.

End Handshake.

Preprocess Module Handshake
  as HandshakePP
       { opaque
           (*
           PArithSeqBool
           PCmpSeq
           PCmpSeqBool
           PLiteralSeqBool
            *)
           CryptolPrimitives.ecAt
           (*
           ecGt
           ecLt
           ecMinus
           ecNotEq
           ecNumber
           ecPlus
           handshakes_fn
           natToNat
            *)
           seq
       }.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in HandshakePP.get_handshake_type
  as getHandshakeType.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in HandshakePP.get_message_number
  as getMessageNumber.

Configure Lift
          HandshakePP.handshake
          HandshakePP.Handshake
          { opaque
              (*
              PArithSeqBool
              PCmpSeq
              PCmpSeqBool
              PLiteralSeqBool
               *)
              CryptolPrimitives.ecAt
              (*
              ecGt
              ecLt
              ecMinus
              ecNotEq
              ecNumber
              ecPlus
              handshakes_fn
              natToNat
               *)
              seq
          }.

Module Connection.

  (**
This is what the original Cryptol [connection] type looked like:

type connection = {handshake : handshake
                  ,mode : [32]
                  ,corked_io : [8]
                  ,corked : [2]
                  ,is_caching_enabled : Bit
                  ,resume_from_cache : Bit
                  ,server_can_send_ocsp : Bit
                  ,key_exchange_eph : Bit
                  ,client_auth_flag : Bit //whether the server will request client cert
                  }

   *)
  Definition connection :=
    ((prod)
       (* client_auth_flag *)
       (@bool)
       (((prod)
           (* corked *)
           (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@bool)))
           (((prod)
               (* corked_io *)
               (((@CryptolPrimitives.seq) (((@TCNum) (8))) (@bool)))
               (((prod)
                   HandshakePP.handshake
                   (*((prod)
                       (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
                       (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool))))*)
                   (((prod)
                       (* is_caching_enabled *)
                       (@bool)
                       (((prod)
                           (* key_exchange_eph *)
                           (@bool)
                           (((prod)
                               (* mode *)
                               (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
                               (((prod)
                                   (* resume_from_cache *)
                                   (@bool)
                                   (* server_can_send_ocsp *)
                                   (@bool)))))))))))))))).

  Record Connection :=
    MkConnection
      {
        clientAuthFlag    : bool;
        corked            : seq 2 bool;
        corkedIO          : seq 8 bool;
        handshake         : HandshakePP.Handshake;
        isCachingEnabled  : bool;
        keyExchangeEPH    : bool;
        mode              : seq 32 bool;
        resumeFromCache   : bool;
        serverCanSendOCSP : bool;
      }.

  Scheme Induction for Connection Sort Prop.
  Scheme Induction for Connection Sort Type.
  Scheme Induction for Connection Sort Set.

  Definition get_client_auth_flag (c : connection) : bool :=
    fst c.

  Definition get_corked (c : connection) : seq 2 bool :=
    fst (snd c).

  Definition get_corked_IO (c : connection) : seq 8 bool :=
    fst (snd (snd c)).

  Definition get_handshake (c : connection) : Handshake.handshake :=
    fst (snd (snd (snd c))).

  Definition get_is_caching_enabled (c : connection) : bool :=
    fst (snd (snd (snd (snd c)))).

  Definition get_key_exchange_EPH (c : connection) : bool :=
    fst (snd (snd (snd (snd (snd c))))).

  Definition get_mode (c : connection) : seq 32 bool :=
    fst (snd (snd (snd (snd (snd (snd c)))))).

  Definition get_resume_from_cache (c : connection) : bool :=
    fst (snd (snd (snd (snd (snd (snd (snd c))))))).

  Definition get_server_can_send_ocsp (c : connection) : bool :=
    snd (snd (snd (snd (snd (snd (snd (snd c))))))).

End Connection.

Preprocess Module Connection
  as ConnectionPP
     { opaque
         seq
         CryptolPrimitives.ecAt
         HandshakePP.handshake
         CryptolPrimitives.seq
         TCNum
     }.

Configure Lift
          HandshakePP.handshake
          HandshakePP.Handshake
          { opaque
              CryptolPrimitives.ecAt
              seq
              CryptolPrimitives.seq
              TCNum
          }.

Definition two := 2.
Definition eight := 8.
Definition thirty_two := 32.
Definition one_twenty_eight := 128.

Replace Convertible Module one_twenty_eight thirty_two eight two in ConnectionPP as ConnectionPP'.

Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.connection               as connectionPP.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.get_client_auth_flag     as getClientAuthFlag0.
Lift connectionPP ConnectionPP'.Connection        in getClientAuthFlag0                    as getClientAuthFlag.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.get_corked               as getCorked0.
Lift connectionPP ConnectionPP'.Connection        in getCorked0                            as getCorked.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.get_corked_IO            as getCorkedIO0.
Lift connectionPP ConnectionPP'.Connection        in getCorkedIO0                          as getCorkedIO.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.get_handshake            as getHandshake0.
Lift connectionPP ConnectionPP'.Connection        in getHandshake0                         as getHandshake.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.get_is_caching_enabled   as getIsCachingEnabled0.
Lift connectionPP ConnectionPP'.Connection        in getIsCachingEnabled0                  as getIsCachingEnabled.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.get_key_exchange_EPH     as getKeyExchangeEPH0.
Lift connectionPP ConnectionPP'.Connection        in getKeyExchangeEPH0                    as getKeyExchangeEPH.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.get_mode                 as getMode0.
Lift connectionPP ConnectionPP'.Connection        in getMode0                              as getMode.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.get_resume_from_cache    as getResumeFromCache0.
Lift connectionPP ConnectionPP'.Connection        in getResumeFromCache0                   as getResumeFromCache.
Lift HandshakePP.handshake HandshakePP.Handshake in ConnectionPP'.get_server_can_send_ocsp as getServerCanSendOCSP0.
Lift connectionPP ConnectionPP'.Connection        in getServerCanSendOCSP0                 as getServerCanSendOCSP.

Module S2N.

  Definition ACTIVE_MESSAGE (conn : ((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@bool)))
  (((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
  (@bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))))) (((prod)
  (@bool) (((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
  (((prod) (@bool) (@bool)))))))))))))))))
  := ((@CryptolPrimitives.ecAt) (((@TCNum) (32))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))) (((@TCNum) (32)))
  (((@CryptolPrimitives.ecAt) (((@TCNum) (128))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (((@CryptolPrimitives.seq) (((@TCNum) (32)))
  (@bool))))) (((@TCNum) (32))) (Vector.const (Vector.const (Vector.const false _) _) _) (((fst) (((fst)
  (((snd) (((snd) (((snd) (conn))))))))))))) (((snd) (((fst) (((snd) (((snd)
  (((snd) (conn)))))))))))).

  Definition advance_message_mini (conn : ((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@bool)))
  (((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
  (@bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))))) (((prod)
  (@bool) (((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
  (((prod) (@bool) (@bool)))))))))))))))))
    := conn.

  Definition advance_message_mini2 (conn : ((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@bool)))
  (((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
  (@bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))))) (((prod)
  (@bool) (((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
  (((prod) (@bool) (@bool)))))))))))))))))
    := fst conn.

  Definition advance_message_mini3 (conn : ((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@bool)))
  (((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
  (@bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))))) (((prod)
  (@bool) (((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
  (((prod) (@bool) (@bool)))))))))))))))))
    := snd conn.

  Definition advance_message_mini4 (conn : ((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@bool)))
  (((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
  (@bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))))) (((prod)
  (@bool) (((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
  (((prod) (@bool) (@bool)))))))))))))))))
    := (((snd) (((snd) (((snd) (((snd) (((snd) (conn))))))))))).

  Definition advance_message_mini5 (conn : ((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@bool)))
  (((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
  (@bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))))) (((prod)
  (@bool) (((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
  (((prod) (@bool) (@bool)))))))))))))))))
    := (((snd) (((snd) (((snd) (((snd) (((snd) (((snd) (conn))))))))))))).

  Definition advance_message_mini6 (conn : ((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@bool)))
  (((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
  (@bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))))) (((prod)
  (@bool) (((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
  (((prod) (@bool) (@bool)))))))))))))))))
    := (((snd) (((snd) (((snd) (((snd) (((snd) (((snd)
  (((snd) (conn))))))))))))))).

  Definition advance_message_mini7 (conn : ((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (2))) (@bool)))
  (((prod) (((@CryptolPrimitives.seq) (((@TCNum) (8)))
  (@bool))) (((prod) (((prod) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))) (((@CryptolPrimitives.seq)
  (((@TCNum) (32))) (@bool))))) (((prod)
  (@bool) (((prod) (@bool) (((prod)
  (((@CryptolPrimitives.seq) (((@TCNum) (32))) (@bool)))
  (((prod) (@bool) (@bool)))))))))))))))))
    := (((pair)
  (((fst) (((snd) (((snd) (((snd) (((snd) (conn))))))))))) (((pair) (((fst)
  (((snd) (((snd) (((snd) (((snd) (((snd) (conn))))))))))))) (((pair) (((fst)
  (((snd) (((snd) (((snd) (((snd) (((snd) (((snd) (conn))))))))))))))) (((pair)
  (((fst) (((snd) (((snd) (((snd) (((snd) (((snd) (((snd) (((snd)
  (conn))))))))))))))))) (((snd) (((snd) (((snd) (((snd) (((snd) (((snd) (((snd)
                           (((snd) (conn))))))))))))))))))))))))).

End S2N.

Preprocess Module S2N
  as S2N'
       { opaque
           CryptolPrimitives.ecAt
           CryptolPrimitives.seq
           TCNum
           Vector.const
           nat_rect
       } .

Configure Lift
          HandshakePP.handshake
          HandshakePP.Handshake
          { opaque
              CryptolPrimitives.ecAt
              CryptolPrimitives.seq
              TCNum
              Vector.const
              nat_rect
          }.

Configure Lift
          connectionPP ConnectionPP'.Connection
          { opaque
              CryptolPrimitives.ecAt
              CryptolPrimitives.seq
              TCNum
              Vector.const
              nat_rect
          }.

Replace Convertible Module one_twenty_eight thirty_two eight two in S2N' as S2N''.

(* Lifting time! *)

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N''.ACTIVE_MESSAGE
  as ActiveMessage_Handshake.

Lift connectionPP ConnectionPP'.Connection
  in ActiveMessage_Handshake
  as ActiveMessage.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N''.advance_message_mini
  as advanceMessageMini_Handshake.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N''.advance_message_mini2
  as advanceMessageMini2_Handshake.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N''.advance_message_mini3
  as advanceMessageMini3_Handshake.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N''.advance_message_mini4
  as advanceMessageMini4_Handshake.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N''.advance_message_mini5
  as advanceMessageMini5_Handshake.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N''.advance_message_mini6
  as advanceMessageMini6_Handshake.

Lift HandshakePP.handshake
     HandshakePP.Handshake
  in S2N''.advance_message_mini7
  as advanceMessageMini7_Handshake.