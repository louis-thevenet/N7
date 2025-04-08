/**
* Conditions initiales
*/

:- dynamic(move/2).
:- dynamic(on/2).

on(a,b).
on(b,c).
on(c, table).

/**
* Précondition : Rien n'est sûr C1 ou C2 (sauf si C2 est la table)
* Postcondition : C1 est sur C2
* 
*/
put_on(C1, C2) :- 
    \+ on(X, C1),
    (C2 == table; \+ on(Y, C2)),
    retract(on(C1, Z)),
    assertz(on(C1,C2)), 
    assertz(move(C1,C2)),
    on(C1,C2).

clear(C):-
    (on(X, C),
    clear(X),
    put_on(X, table),
    clear(C));
    
    \+ on(X, C).

r_put_on(C1,C2) :- 
    clear(C1),
    clear(C2), 
    put_on(C1,C2).

achieve(L) :- 
    L = [H|Q],
    (H = on(A,B), 
    (r_put_on(A,B) , achieve(Q)));
    
    L == [], listing(move).

/* L'execution de achieve([on(a,c), on(c,b)]) met en lumière une limitation de la fonction achieve :

move(a, table).
move(b, table).
move(a, c).
move(a, table).  <--- On défait ce qu'on a fait précémment
move(c, b).
move(c, table).
move(c, b).

La situation finale n'est pas correcte:
Initiale   |   Finale
a          |
b          |           c
c          |  a        b    
table      |  table    table */
   
/* Relation transitive de dépendance */
depends_on(C1, C2) :- on(C1, C2).
depends_on(C1, C2) :- on(C1, X), depends_on(X, C2).

sort_goals([], []).
sort_goals([G | R], Sorted) :-
    sort_goals(R, PartialSorted),
    insert_sorted(G, PartialSorted, Sorted).

insert_sorted(G, [], [G]).
insert_sorted(G, [H | T], [G, H | T]) :- 
    G = on(A, _), H = on(B, _), 
    \+ depends_on(A, B).
insert_sorted(G, [H | T], [H | Sorted]) :- 
    insert_sorted(G, T, Sorted).

achievev2(L) :-
    sort_goals(L, Sorted),
    achieve(Sorted).

/*
Pour l'execution de achieve([on(a,c), on(c,b)]), on obtient:

move(a, table).
move(b, table).
move(c, b).
move(a, c).

La solution finale est correcte.
Initiale   |   Finale
a          |  a
b          |  c
c          |  b    
table      |  table
*/
    
