------------------------- MODULE PCalAlternatingBit -------------------------
EXTENDS Integers, Sequences

Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]
CONSTANT
  Data
  
(*
--algorithm PCalAlternatingBit
  variable
    AtoB = << >>;
    BtoA = << >>;
    
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
    
    fair process Sender = 1
    variable
      AVar \in Data \X {0}; 
      b = 0;     
    begin
s1:   while TRUE do
s2:+    Snd(AtoB, AVar);
s3:     either 
          Rcv(BtoA, b);
          if b = AVar[2] then
            with d \in Data do
              AVar := <<d, 1 - AVar[2]>>;
            end with
          end if
        or
          skip;    \* timeout and resend
        end either
      end while
    end process
    
    fair process Receiver = 2
    variable
      BVar \in Data \X {1};
      msg = BVar;    
    begin
r1:   while TRUE do
r2:     either
          Rcv(AtoB, msg);
          if msg[2] /= BVar[2] then
            BVar := msg;
          end if;
        or
          skip;    \* timeout and resend
        end either;
r3:+    Snd(BtoA, msg[2]);
      end while
    end process
    
    process Demon = 3
    begin
d:    await AtoB /= << >>;
      with i \in 1..Len(AtoB) do
        AtoB := Remove(i, AtoB);
      end with
    end process
end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES AtoB, BtoA, pc, AVar, b, BVar, msg

vars == << AtoB, BtoA, pc, AVar, b, BVar, msg >>

ProcSet == {1} \cup {2} \cup {3}

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
                                        [] self = 2 -> "r1"
                                        [] self = 3 -> "d"]

s1 == /\ pc[1] = "s1"
      /\ pc' = [pc EXCEPT ![1] = "s2"]
      /\ UNCHANGED << AtoB, BtoA, AVar, b, BVar, msg >>

s2 == /\ pc[1] = "s2"
      /\ AtoB' = Append(AtoB, AVar)
      /\ pc' = [pc EXCEPT ![1] = "s3"]
      /\ UNCHANGED << BtoA, AVar, b, BVar, msg >>

s3 == /\ pc[1] = "s3"
      /\ \/ /\ BtoA /= << >>
            /\ b' = Head(BtoA)
            /\ BtoA' = Tail(BtoA)
            /\ IF b' = AVar[2]
                  THEN /\ \E d \in Data:
                            AVar' = <<d, 1 - AVar[2]>>
                  ELSE /\ TRUE
                       /\ AVar' = AVar
         \/ /\ TRUE
            /\ UNCHANGED <<BtoA, AVar, b>>
      /\ pc' = [pc EXCEPT ![1] = "s1"]
      /\ UNCHANGED << AtoB, BVar, msg >>

Sender == s1 \/ s2 \/ s3

r1 == /\ pc[2] = "r1"
      /\ pc' = [pc EXCEPT ![2] = "r2"]
      /\ UNCHANGED << AtoB, BtoA, AVar, b, BVar, msg >>

r2 == /\ pc[2] = "r2"
      /\ \/ /\ AtoB /= << >>
            /\ msg' = Head(AtoB)
            /\ AtoB' = Tail(AtoB)
            /\ IF msg'[2] /= BVar[2]
                  THEN /\ BVar' = msg'
                  ELSE /\ TRUE
                       /\ BVar' = BVar
         \/ /\ TRUE
            /\ UNCHANGED <<AtoB, BVar, msg>>
      /\ pc' = [pc EXCEPT ![2] = "r3"]
      /\ UNCHANGED << BtoA, AVar, b >>

r3 == /\ pc[2] = "r3"
      /\ BtoA' = Append(BtoA, (msg[2]))
      /\ pc' = [pc EXCEPT ![2] = "r1"]
      /\ UNCHANGED << AtoB, AVar, b, BVar, msg >>

Receiver == r1 \/ r2 \/ r3

d == /\ pc[3] = "d"
     /\ AtoB /= << >>
     /\ \E i \in 1..Len(AtoB):
          AtoB' = Remove(i, AtoB)
     /\ pc' = [pc EXCEPT ![3] = "Done"]
     /\ UNCHANGED << BtoA, AVar, b, BVar, msg >>

Demon == d

Next == Sender \/ Receiver \/ Demon

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Sender) /\ SF_vars(s2)
        /\ WF_vars(Receiver) /\ SF_vars(r3)

\* END TRANSLATION

TypeOK == 
  /\ AtoB \in Seq(Data \X {0,1})
  /\ BtoA \in Seq({0, 1})
  /\ AVar \in Data \X {0, 1}
  /\ BVar \in Data \X {0, 1}
  /\ b \in {0, 1}
  /\ msg \in Data \X {0, 1}
  
Live == \A m \in Data \X {0, 1} : AVar = m ~> BVar = m
=============================================================================
\* Modification History
\* Last modified Wed Nov 07 18:51:25 GMT 2018 by cgdk2
\* Created Wed Nov 07 16:20:26 GMT 2018 by cgdk2
