---------------- MODULE jeton ----------------
\* Time-stamp: <09 oct 2024 11:55 Philippe Queinnec>

(* Algorithme d'exclusion mutuelle à base de jeton. *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANT N

ASSUME N \in Nat /\ N > 1

Processus == 0..N-1

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
  canal,
  etat,
  jeton

TypeOK ==
   [] (/\ etat \in [ Processus -> {Hungry,Thinking,Eating} ]
       /\ jeton \in [Processus -> BOOLEAN]
       /\ canal \in [Processus ->Seq(BOOLEAN)]
       )

Sanity ==
  [] (\A i \in Processus : etat[i] = Eating => jeton[i])

----------------------------------------------------------------

Init ==
 /\ etat = [ i \in Processus |-> Thinking ]
 /\ \E i \in Processus: jeton = [j \in Processus |-> i=j]
 /\ canal = [i \in Processus |-> (Append(Seq(FALSE), FALSE))]
 
demander(i) ==
  /\ etat[i] = Thinking
  /\ etat' = [ etat EXCEPT ![i] = Hungry ]
  /\ UNCHANGED jeton

entrer(i) ==
  /\ etat[i] = Hungry
  /\ jeton[i]
  /\ etat' = [ etat EXCEPT ![i] = Eating ]
  /\ UNCHANGED jeton

sortir(i) ==
  /\ etat[i] = Eating
  /\ etat' = [ etat EXCEPT ![i] = Thinking ]
  (*/\ canal' = [canal EXCEPT ![i] = Append(Tail(canal[i]), TRUE)]*)
  /\ canal' = [canal EXCEPT ![i] =   (Append(Seq(TRUE), FALSE))]
  
  
bouger(i) ==
  /\ jeton[i]
  /\ etat[i] = Thinking
  /\ canal' = [canal EXCEPT ![i] =   (Append(Seq(TRUE), FALSE))]
  /\ UNCHANGED etat

EnvoiJeton(i) == 
    /\ Head(canal[i]) 
    /\ canal' = [canal EXCEPT ![i] = (Append(Seq(TRUE), TRUE))]
    
ReceptionJeton(i) == 
    /\ Tail(canal[i])
    /\ canal' = [canal EXCEPT ![(i-1)%N] = (Append(Seq(FALSE), FALSE))]
    /\ jeton' = [jeton EXCEPT ![i]=FALSE, ![(i+1)%N]=TRUE]


Next ==
 \E i \in Processus :
    \/ demander(i)
    \/ entrer(i)
    \/ sortir(i)
    \/ bouger(i)
    \/ EnvoiJeton(i)
    \/ ReceptionJeton(i)

Fairness == \A i \in Processus :
              /\ WF_<<etat,jeton>> (sortir(i))
              /\ WF_<<etat,jeton>> (bouger(i))
FairnessQ2 == 
    \A i \in Processus :
          /\ SF_<<etat, jeton>> (entrer(i))
          /\ SF_<<etat,jeton>> (bouger(i))
          /\ WF_<<etat,jeton>> (sortir(i))
          
          
FairnessQ3 == 
    \A i \in Processus :
          /\ WF_<<etat, jeton>> (entrer(i))
          /\ WF_<<etat, jeton>> (sortir(i))
          /\ WF_<<etat, jeton>> (bouger(i))
          
      
Spec ==
 /\ Init
 /\ [] [ Next ]_<<etat,jeton>>
 /\ FairnessQ3



ExclMutuelle == [] (Cardinality({i \in Processus : etat[i] = Eating}) <= 1) 

VivaciteIndividuelle == (\A i \in Processus: etat[i] = Hungry ~> etat[i] = Eating)

VivaciteGlobale == (Cardinality({i \in Processus : etat[i] = Hungry}) > 0) ~> (Cardinality({i \in Processus : etat[i] = Eating}) > 0) 

JetonVaPartout == (\A i \in Processus: []<> (jeton[i]))

UniciteJeton == [] (Cardinality({i \in Processus: jeton[i]}) = 1)

UnSeulEnvoi == [] (Cardinality({i \in Processus: Head(canal[i])}) <= 1)
UneSeuleReception == [] (Cardinality({i \in Processus: Head(canal[i])}) <= 1)

(*Raffinage version tableau de booléen de simple entier*)
(*etat |-> etat*)
(*jeton |-> CHOOSE {i \in Processus: jeton[i]}*)

================
