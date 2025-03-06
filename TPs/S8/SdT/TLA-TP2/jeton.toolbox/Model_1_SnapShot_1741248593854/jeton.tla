---------------- MODULE jeton ----------------
\* Time-stamp: <09 oct 2024 11:55 Philippe Queinnec>

(* Algorithme d'exclusion mutuelle à base de jeton. *)

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 1

Processus == 0..N-1

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
  etat,
  jeton

TypeOK ==
   [] (/\ etat \in [ Processus -> {Hungry,Thinking,Eating} ]
       /\ jeton \in Processus)



Sanity ==
  [] (\A i \in Processus : etat[i] = Eating => jeton = i)

----------------------------------------------------------------

Init ==
 /\ etat = [ i \in Processus |-> Thinking ]
 /\ jeton \in Processus

demander(i) ==
  /\ etat[i] = Thinking
  /\ etat' = [ etat EXCEPT ![i] = Hungry ]
  /\ UNCHANGED jeton

entrer(i) ==
  /\ etat[i] = Hungry
  /\ jeton = i
  /\ etat' = [ etat EXCEPT ![i] = Eating ]
  /\ UNCHANGED jeton

sortir(i) ==
  /\ etat[i] = Eating
  /\ etat' = [ etat EXCEPT ![i] = Thinking ]
  /\ UNCHANGED jeton

bouger(i) ==
  /\ jeton = i
  /\ etat[i] # Eating
  /\ jeton' = (i+1)%N
  /\ UNCHANGED etat

Next ==
 \E i \in Processus :
    \/ demander(i)
    \/ entrer(i)
    \/ sortir(i)
    \/ bouger(i)

Fairness == \A i \in Processus :
              /\ WF_<<etat,jeton>> (sortir(i))
              /\ WF_<<etat,jeton>> (bouger(i))
FairnessQ2 == 
    \A i \in Processus :
          /\ SF_<<etat, jeton>> (entrer(i))
          /\ SF_<<etat,jeton>> (bouger(i))
          
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

JetonVaPartout == (\A i \in Processus: []<> (jeton=i))
================
