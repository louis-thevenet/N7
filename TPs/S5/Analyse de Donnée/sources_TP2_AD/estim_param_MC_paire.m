% fonction estim_param_MC_paire (pour exercice_2.m)

function parametres = estim_param_MC_paire(d,x,y_inf,y_sup)
    p = size(x,1);

    A_j = zeros(p*2, 2*d-1);
    for j=1:d-1 
        A_j(1:p, j) = vecteur_bernstein(x, d, j);
    end

    for j=d:2*d-1 
        A_j(p+1:2*p, j) = vecteur_bernstein(x, d, j-d+1);
    end

    A_j(1:p, end)=vecteur_bernstein(x, d, d);
    B_j = zeros(2*p,1);
    B_j(1:p) = y_inf - y_inf(1) .* (1-x).^d;
    B_j(p+1:2*p) = y_sup - y_sup(1) .* (1-x).^d;
   
    parametres = (A_j\B_j);

end
