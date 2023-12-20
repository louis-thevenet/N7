% Fonction estim_param_Dyx_MC (exercice_1.m)

function [a_Dyx,b_Dyx] = ...
                   estim_param_Dyx_MC(x_donnees_bruitees,y_donnees_bruitees)


  
    A(1, :) = x_donnees_bruitees';
    A(2,:) = ones(size(y_donnees_bruitees, 1), 1)';
    A=A';

    B = y_donnees_bruitees;

    X = ((A'*A)\A') * B;

    a_Dyx=X(1);
    b_Dyx=X(2);

end