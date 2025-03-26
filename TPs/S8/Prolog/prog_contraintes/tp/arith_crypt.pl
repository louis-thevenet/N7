
add(D, O, N, A, L, B, G, E, R, T) :-
    fd_domain([O, N, A, L, B, E, T], 0,9),
    fd_domain([D, G, R], 1,9),
    D * 100000 + O * 10000 + N * 1000 + A * 100 + L * 10 + D
    + G * 100000 + E * 10000 + R * 1000 + A * 100 + L * 10 + D
    #= R * 100000 + O * 10000 + B * 1000 + E * 100 + R * 10 + T,
fd_all_different([D, O, N, A, L, B, G, E, R, T]),
fd_labeling([D, O, N, A, L, B, G, E, R, T])
    
    
    .
    
