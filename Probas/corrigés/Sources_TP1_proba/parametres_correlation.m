% Fonction parametres_correlation (exercice_1.m)

function [r,a,b] = parametres_correlation(Vd,Vg)
    moy_d = mean(Vd);
    var_d = mean((Vd - moy_d).^2);

    moy_g = mean(Vg);
    var_g = mean((Vg - moy_g).^2);

    covar = mean((Vd - moy_d).*(Vg - moy_g));

    r = covar/sqrt(var_d*var_g);
    a = covar/var_d; % g = X
    b = moy_g - a*moy_d;
end