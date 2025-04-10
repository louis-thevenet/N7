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
 
 
deprecated_solve(Num, Xs, Ys) :-
    data(Num, T, Ts),
    length(Ts, N),
    length(Xs, N),
    length(Ys, N),
 
    within_bounds(Xs, Ys, Ts, T),
 
    noverlap(Xs, Ys, Ts),
 
    fd_labeling(Xs),
    fd_labeling(Ys),
 
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

solve(Num, Xs, Ys, B, B2) :-
    data(Num, T, Ts),
    length(Ts, N),
    length(Xs, N),
    length(Ys, N),

    % Ajout des contraintes redondantes
    T1 is T-1,
    sum_verticals(Xs, Ys, Ts, T, T1),
    sum_horizontals(Xs, Ys, Ts, T, T1 ),

    within_bounds(Xs, Ys, Ts, T),
    noverlap(Xs, Ys, Ts),

    fd_labeling(Ys, [backtracks(B)]),
    fd_labeling(Xs, [backtracks(B2)]),

    % Appel à printsol pour écrire la solution dans un fichier
    printsol('tiles.txt', Xs, Ys, Ts).
