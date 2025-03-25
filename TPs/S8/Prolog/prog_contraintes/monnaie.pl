monnaie(Cost, UnC, DeuxC, Cinq, Dix, Vingt, Cinquante, UnE, DeuxE) :-
    
    fd_domain([UnC, DeuxC, Cinq, Dix, Vingt, Cinquante, UnE, DeuxE],0,3 ),
    fd_domain([Cost], 0, 24),

    UnC + DeuxC * 2 + Cinq * 5 + Dix*10 + Vingt *20  + Cinquante * 50 + UnE * 100 + DeuxE * 200 #= 2000-1729,
    sum([UnC, DeuxC, Cinq, Dix, Vingt, Cinquante, UnE, DeuxE], Cost),
    fd_minimize(fd_labeling([Cost,UnC, DeuxC, Cinq, Dix, Vingt, Cinquante, UnE, DeuxE]), Cost).
    

sum([], 0).
sum([H|T], S) :- sum(T, S2), S #= H+S2. 

