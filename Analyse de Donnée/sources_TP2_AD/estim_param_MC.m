% fonction estim_param_MC (pour exercice_1.m)

function parametres = estim_param_MC(d,x,y)

    A_j = zeros(size(x, 1), d);
    for j=1:d 
        A_j(:, j) = vecteur_bernstein(x, d, j);
    end
    B_j = y - y(1) .* (1-x).^d;
    parametres = (A_j\B_j);
end
