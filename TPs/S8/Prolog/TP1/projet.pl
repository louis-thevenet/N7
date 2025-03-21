est_sur(a,b).
est_sur(b,c).
est_sur(c, table).

/**
* Précondition : Rien n'est sûr C1 ou C2 (sauf si C2 est la table)
 * Postcondition : C1 est sur C2
 * 
*/
put_on(C1, C2) :- 
    \+ est_sur(X, C1),
    (C2 == table; \+ est_sur(Y, C2)),
    retract(est_sur(C1, Z)),
    assertz( est_sur(C1,C2)), 
    assertz(move(C1,C2)),
    est_sur(C1,C2).

clear(C):-
    (est_sur(X, C), clear(X), put_on(X, table), clear(C)); \+ est_sur(X, C).

r_put_on(C1,C2) :- 
    clear(C1), clear(C2), put_on(C1,C2).

achieve()