volumes(L):-
	L =
       [1919,609,869,1244,490,1400,1100,1892,775,1449,1180,72,1044,599,1941,
	1331,781,1773,1242,1566,1713,1476,1677,845,144,17,842,215,161,1045,
	530,860,822,862,154,752,1592,363,1685,490,250,1099,795,31,1429,932,
	1241,286,1217,705,84,3].

valeurs(L):-
	L =
       [2195,2219,1673,1792,2777,916,664,737,1372,2000,235,2975,790,2650,
	2857,68,1045,2946,1314,1839,44,363,2450,2339,1284,1449,1762,2963,
	208,2986,751,1271,1173,342,1458,488,101,1033,2917,2188,616,2959,
	1722,2942,818,1948,602,2711,514,2007,2597,2736].

capacite_max(2000).

cost([], [], 0).
cost([B|TB], [V|VB], S) :- cost(TB, VB,S2), S #= S2 + V*B. 

same_length([],[]).
same_length([H|T], [H2|T2]) :- same_length(T,T2).


fret(Bo) :-
    volumes(Vo),
    valeurs(Va),
    same_length(Bo, Va),
    fd_domain(Bo, 0,1),

    cost(Bo, Vo, VolumeTotal),
    cost(Bo, Va, ValeurTotale),
    capacite_max(CapaciteMax),
    VolumeTotal #=< CapaciteMax,
    fd_maximize(fd_labeling(Bo,[value_method(max)]),ValeurTotale).
    % max c'est mieux que min et c'est logique


