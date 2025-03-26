taxi(N,A,B,C,D) :-
    fd_domain([N], 0, 1000000),
    fd_domain([A, B, C, D], 0, 100),
    N #= A*A*A + B*B*B,
    N #= C*C*C + D*D*D,
    A #\= C,
    B #\= D,
    A #\= D,
    B #\= C,
    fd_minimize(fd_labeling([N,A,B,C,D]), N).


