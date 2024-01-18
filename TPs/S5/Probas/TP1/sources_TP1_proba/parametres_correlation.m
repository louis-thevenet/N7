% Fonction parametres_correlation (exercice_1.m)

function [r,a,b] = parametres_correlation(Vd,Vg)
  

    sigma_x = sqrt( sum(Vd.*Vd) / size(Vd, 1) - mean(Vd)*mean(Vd) );
   
    sigma_y = sqrt( sum(Vg.*Vg) / size(Vg, 1) - mean(Vg)*mean(Vg) );

    sigma_xy = (Vg' * Vd)/size(Vg, 1) - mean(Vg)*mean(Vd);
    r = sigma_xy / (sigma_x*sigma_y);

    a = sigma_xy / (sigma_x*sigma_x);
    b = mean(Vg)-a * mean(Vg);
end