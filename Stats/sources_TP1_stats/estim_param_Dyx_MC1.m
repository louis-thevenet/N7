% Fonction estim_param_Dyx_MC1 (exercice_2.m)

function [a_Dyx,b_Dyx,coeff_R2] = ...
                   estim_param_Dyx_MC1(x_donnees_bruitees,y_donnees_bruitees)

    [~, y_G, ~,~] = centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees);

    A(1, :) = x_donnees_bruitees';
    A(2,:) = ones(size(y_donnees_bruitees, 1), 1)';
    A=A';

    B = y_donnees_bruitees;

    X = ((A'*A)\A') * B;

    a_Dyx=X(1);
    b_Dyx=X(2);

    coeff_R2 = 1 - ((y_donnees_bruitees-a_Dyx * x_donnees_bruitees-b_Dyx)'*(y_donnees_bruitees-a_Dyx * x_donnees_bruitees-b_Dyx)) / ((y_donnees_bruitees-y_G)'*(y_donnees_bruitees-y_G));
end