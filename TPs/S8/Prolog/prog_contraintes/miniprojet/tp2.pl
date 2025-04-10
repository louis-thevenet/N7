:- include(libtp2).
 
%Modèle Basique
%1)

interval(_, [], _, [], _, []).
interval(X, [Xl|Xls], Y, [Yl|Yls], T, [Tl|Tls]) :-
    (Xl #>= X + T #\/
    Xl + Tl #=< X #\/
    Yl #>= Y + T #\/
    Yl + Tl #=< Y),
    interval(X, Xls, Y, Yls, T, Tls).
 
noverlap([], [], []).
noverlap([X|Xs], [Y|Ys],[T|Ts]):-
    interval(X, Xs, Y,Ys,T, Ts),
    noverlap(Xs, Ys, Ts).
 
within_bounds([], [], [], _).
within_bounds([X|Xs], [Y|Ys], [T|Ts], Max) :-
    TailleMax is Max - T,
    fd_domain(X, 0, TailleMax),
    fd_domain(Y, 0, TailleMax),
    within_bounds(Xs, Ys, Ts, Max).
 
 
solve_1(Num, Xs, Ys, Bx, By) :-
    data(Num, T, Ts),
    length(Ts, N),
    length(Xs, N),
    length(Ys, N),
 
    within_bounds(Xs, Ys, Ts, T),
 
    noverlap(Xs, Ys, Ts),
 
    fd_labeling(Xs, [backtracks(Bx)]),
    fd_labeling(Ys, [backtracks(By)]),
 
    % 2) Appel à printsol pour écrire la solution dans un fichier
    printsol('tiles.txt', Xs, Ys, Ts).

% Contraintes redondantes
% 1)

sum_verticals(_, _, _, _, 0). 
sum_verticals(Xs, Ys, Ts, T, V) :-
    sum_verticals_aux(Xs, Ys, Ts, V, 0, Sum),
    Sum #= T,
    V1 is V - 1,
    sum_verticals(Xs, Ys, Ts, T, V1).

sum_verticals_aux([], [], [], _, Acc, Acc).
sum_verticals_aux([Xl|Xls], [Yl|Yls], [Tl|Tls], V, Acc, Sum) :-
    (Xl #=< V #/\ V #< Xl + Tl) #<=> InRange,
    NewAcc #= Acc + InRange * Tl,
    sum_verticals_aux(Xls, Yls, Tls, V, NewAcc, Sum).

sum_horizontals(_, _, _, _, 0).
sum_horizontals(Xs, Ys, Ts, T, H) :-
    sum_horizontals_aux(Xs, Ys, Ts, H, 0, Sum),
    Sum #= T,
    H1 is H - 1,
    sum_horizontals(Xs, Ys, Ts, T, H1).

sum_horizontals_aux([], [], [], _, Acc, Acc).
sum_horizontals_aux([Xl|Xls], [Yl|Yls], [Tl|Tls], H, Acc, Sum) :-
    (Yl #=< H #/\ H #< Yl + Tl) #<=> InRange,
    NewAcc #= Acc + InRange * Tl,
    sum_horizontals_aux(Xls, Yls, Tls, H, NewAcc, Sum).

solve_2(Num, Xs, Ys, Bx, By) :-
    data(Num, T, Ts),
    length(Ts, N),
    length(Xs, N),
    length(Ys, N),

    within_bounds(Xs, Ys, Ts, T),
    noverlap(Xs, Ys, Ts),

    % Ajout des contraintes redondantes
    T1 is T-1,
    sum_verticals(Xs, Ys, Ts, T, T1),
    sum_horizontals(Xs, Ys, Ts, T, T1 ),

    fd_labeling(Xs, [backtracks(Bx)]),
    fd_labeling(Ys, [backtracks(By)]),

    % Appel à printsol pour écrire la solution dans un fichier
    printsol('tiles.txt', Xs, Ys, Ts).

% 2)
% Pour la version sans contraintes redondantes, on constate que le nombre de backtracks sur Xs (Bx) alterne entre 2 et plus rarement 12, et ce sont les backtracks sur les Ys qui varient de 0 à la taille max du carré.
% Tandis que pour la version avec contraintes redondantes, Xs vaut en moyenne 12 et Ys continue de varier en croissant. 

% L'ajout de ces contraintes permet de mieux réduire l'espace de recherche et de trouver une solution plus rapidement.

% Stratégie de recherche
% 1)

solve_3(Num, Xs, Ys, B, NbSol) :-
    data(Num, T, Ts),
    length(Ts, N),
    length(Xs, N),
    length(Ys, N),

    within_bounds(Xs, Ys, Ts, T),
    noverlap(Xs, Ys, Ts),

    % Ajout des contraintes redondantes
    T1 is T-1,
    sum_verticals(Xs, Ys, Ts, T, T1),
    sum_horizontals(Xs, Ys, Ts, T, T1 ),

    labeling(Xs, Ys, assign, minmin, B, NbSol),

    % Appel à printsol pour écrire la solution dans un fichier
    printsol('tiles.txt', Xs, Ys, Ts).

