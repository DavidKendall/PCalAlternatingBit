------------------------- MODULE PCalAlternatingBit -------------------------
EXTENDS Integers, Sequences

(* Remove element i from sequence seq *)
Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]
CONSTANT
  Data  \* The set of data items that may be transmitted
  
(*
  
  \* A Pluscal model of the alternating bit protocol
  
--algorithm PCalAlternatingBit
  variable
    (* 
      Messages are sent from the sender to the receiver on the AtoB
      channel. Acknowledgements are sent from the receiver to the
      sender on the BtoA channel
    *)       
    AtoB = << >>;
    BtoA = << >>;
    
    (* 
      Macros for sending and receiving messages
    *) 
    macro Snd(c, m)
    begin
      c := Append(c, m);
    end macro;
    
    macro Rcv(c, v)
    begin
      await c /= << >>;
      v := Head(c);
      c := Tail(c);
    end macro;
    
    \* The Sender Process 
    process Sender = 1
    variable
      AVar \in Data \X {0}; \* The message to be sent 
      b = 0;                \* The acknowledgement bit to be received
    begin
s1:   while TRUE do
s2:     Snd(AtoB, AVar); \* Transmit the current message
s3:     either 
          (*
            Receive an acknowledgement bit, check that it matches
            the transmitted protocol bit. If so, generate a new
            message to transmit (the new message data should be chosen 
            non-deterministically from the set Data; the message protocol
            bit should be the inverse of the message protocol bit on the
            current message
          *)
          skip; \* replace this skip statement with the Pluscal code for behaviour above
        or
          skip; \* keep this skip statement to indicate a timeout and retransmission
        end either
      end while
    end process
    
    process Receiver = 2
    variable
      (*
        BVar is used to store a valid message when received. The protocol bit is the
        inverse of the protocol bit that is expected on the next valid message
      *)
      BVar \in Data \X {1}; 
      (*
        msg is a variable that is used to receive a message and to
        check whether or not it is valid. If the message is valid, it
        should be copied from msg to BVar, otherwise it should be discarded
      *)
      msg = BVar;    
    begin
r1:   while TRUE do
r2:     either
          (* 
            Receive a message from the AtoB channel into the msg variable.
            Check if the protocol bit on the received message is different
            from the protocol bit in BVar. If so, this is a valid message and
            should be assigned to BVar. If not it should be ignored.
          *)
          skip; \* replace this skip statement with the Pluscal code for the behaviour above
        or
          skip; \* timeout and resend
        end either;
        (*
          The protocol bit in msg (i.e. msg[2]) is the protocol bit of the
          message that has just bee received. Whether or not the message was
          valid, this is the correct bit to return as the acknowledgement bit.
          Step r3 accomplishes this - there is no more for you to do here.
        *)
r3:     Snd(BtoA, msg[2]);
      end while
    end process

end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES AtoB, BtoA, pc, AVar, b, BVar, msg

vars == << AtoB, BtoA, pc, AVar, b, BVar, msg >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ AtoB = << >>
        /\ BtoA = << >>
        (* Process Sender *)
        /\ AVar \in Data \X {0}
        /\ b = 0
        (* Process Receiver *)
        /\ BVar \in Data \X {1}
        /\ msg = BVar
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "s1"
                                        [] self = 2 -> "r1"]

s1 == /\ pc[1] = "s1"
      /\ pc' = [pc EXCEPT ![1] = "s2"]
      /\ UNCHANGED << AtoB, BtoA, AVar, b, BVar, msg >>

s2 == /\ pc[1] = "s2"
      /\ AtoB' = Append(AtoB, AVar)
      /\ pc' = [pc EXCEPT ![1] = "s3"]
      /\ UNCHANGED << BtoA, AVar, b, BVar, msg >>

s3 == /\ pc[1] = "s3"
      /\ \/ /\ TRUE
         \/ /\ TRUE
      /\ pc' = [pc EXCEPT ![1] = "s1"]
      /\ UNCHANGED << AtoB, BtoA, AVar, b, BVar, msg >>

Sender == s1 \/ s2 \/ s3

r1 == /\ pc[2] = "r1"
      /\ pc' = [pc EXCEPT ![2] = "r2"]
      /\ UNCHANGED << AtoB, BtoA, AVar, b, BVar, msg >>

r2 == /\ pc[2] = "r2"
      /\ \/ /\ TRUE
         \/ /\ TRUE
      /\ pc' = [pc EXCEPT ![2] = "r3"]
      /\ UNCHANGED << AtoB, BtoA, AVar, b, BVar, msg >>

r3 == /\ pc[2] = "r3"
      /\ BtoA' = Append(BtoA, (msg[2]))
      /\ pc' = [pc EXCEPT ![2] = "r1"]
      /\ UNCHANGED << AtoB, AVar, b, BVar, msg >>

Receiver == r1 \/ r2 \/ r3

Next == Sender \/ Receiver

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Nov 09 11:21:25 GMT 2018 by cgdk2
\* Created Wed Nov 07 16:20:26 GMT 2018 by cgdk2
