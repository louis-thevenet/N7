% Fonction estim_param_Dyx_MC2 (exercice_2bis.m)

function [a_Dyx,b_Dyx,coeff_r2] = ...
                   estim_param_Dyx_MC2(x_donnees_bruitees,y_donnees_bruitees)

[x_G, y_G, ~, ~] = centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees);

var_x = ( sum(x_donnees_bruitees.*x_donnees_bruitees) / size(x_donnees_bruitees, 1) - mean(x_donnees_bruitees)*mean(x_donnees_bruitees) );

var_y = ( sum(y_donnees_bruitees.*y_donnees_bruitees) / size(y_donnees_bruitees, 1) - mean(y_donnees_bruitees)*mean(y_donnees_bruitees) );

sigma_xy = (x_donnees_bruitees' * y_donnees_bruitees)/size(x_donnees_bruitees, 1) - mean(x_donnees_bruitees)*mean(y_donnees_bruitees);

coeff_r2 = sigma_xy / (sqrt(var_x * var_y));

a_Dyx = coeff_r2 * sqrt(var_y/var_x);
b_Dyx = y_G - a_Dyx*x_G;
    
end