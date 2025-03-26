:- include(libtp2).
 
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
 
 
solve(Num, Xs, Ys) :-
    data(Num, T, Ts),
    length(Ts, N),
    length(Xs, N),
    length(Ys, N),
 
    within_bounds(Xs, Ys, Ts, T),
 
    noverlap(Xs, Ys, Ts),
 
    fd_labeling(Xs),
    fd_labeling(Ys).