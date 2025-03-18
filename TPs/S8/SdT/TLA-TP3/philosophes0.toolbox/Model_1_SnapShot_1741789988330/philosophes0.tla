---------------- MODULE philosophes0 ----------------
(* Philosophes. Version en utilisant l'état des voisins. *)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1
 
gauche(i) == (i+1)%N       \* philosophe à gauche du philo n°i
droite(i) == (i+N-1)%N     \* philosophe à droite du philo n°i

Hungry == "H"
Thinking == "T"
Eating == "E"

UsedLeft == "usedLeft"
UsedRight == "usedRight"
NotUsed == "notUsed"

VARIABLES
    etat,         \* i -> Hungry,Thinking,Eating
    forks

TypeOK == 
    /\ [](etat \in [ Philos -> { Hungry, Thinking, Eating }])
    /\ [](forks \in [Philos -> {UsedLeft, UsedRight, NotUsed}])

(* TODO : autres propriétés de philosophes0 (exclusion, vivacité) *)  

----------------------------------------------------------------

Init == 
    /\ etat = [p \in Philos |-> Thinking]
    /\ forks = [f \in Philos |-> NotUsed]

prendreDroite(i) == 
    (*/\ (IF i%2 = 1 THEN forks[i] = UsedRight ELSE TRUE)*)   
/\ forks[droite(droite(i))] = NotUsed
    /\ etat[i] = Hungry 
    /\ (forks[droite(i)] # UsedRight)
    /\ forks' = [forks EXCEPT ![droite(i)] = UsedLeft]
    /\ UNCHANGED etat
    
prendreGauche(i) ==
    (*/\ (IF i%2 =1 THEN forks[droite(i)] = UsedLeft ELSE TRUE)*)
    /\ forks[gauche(i)] = NotUsed    
    /\ etat[i] = Hungry 
    /\ (forks[i] # UsedLeft)
    /\ forks' = [forks EXCEPT ![i] = UsedRight]
    /\ UNCHANGED etat

demander(i) ==
    /\ etat[i]= Thinking 
    /\ etat' = [etat EXCEPT ![i] = Hungry]
    /\ UNCHANGED forks

manger(i) == 
    /\ etat[i] = Hungry
    /\ forks[i] = UsedRight
    /\ forks[droite(i)] = UsedLeft
    /\ etat' = [etat EXCEPT ![i] = Eating]
    /\ UNCHANGED forks
    (*
    /\ etat[gauche(i)] # Eating
    /\ etat[droite(i)] # Eating
    *)

penser(i) == 
    /\ etat[i] = Eating
    /\ forks' = [forks EXCEPT ![droite(i)] = NotUsed, ![i]=NotUsed]    
    /\ etat' = [etat EXCEPT ![i] = Thinking]

Next ==
  \E i \in Philos : \/ demander(i)
                    \/ manger(i)
                    \/ penser(i)
                                        
                    \/ prendreGauche(i)
                    \/ prendreDroite(i)

Fairness == \A p \in Philos: 
    /\ WF_<<etat,forks>>(manger(p))
    /\ WF_<<etat,forks>>(penser(p))
    
    /\ WF_<<etat,forks>>(prendreGauche(p))
    /\ WF_<<etat,forks>>(prendreDroite(p))

Spec ==
  /\ Init
  /\ [] [ Next ]_<<etat, forks>>
  /\ Fairness
  
  PasDeFamine ==[](\forall p \in Philos: etat[p] = Hungry ~> etat[p] = Eating)
   ExclusionMutuelle == [](
   \A p \in Philos: (etat[p] = Eating => (etat[droite(p)] # Eating /\ etat[gauche(p)]#Eating))
   )
================================
