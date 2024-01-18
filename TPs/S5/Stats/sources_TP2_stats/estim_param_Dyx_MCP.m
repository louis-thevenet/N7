% Fonction estim_param_Dyx_MCP (exercice_4.m)

function [a_Dyx,b_Dyx] = estim_param_Dyx_MCP(x_donnees_bruitees,y_donnees_bruitees,probas_classe)

    
    A(1, :) = x_donnees_bruitees';
    A(2,:) = ones(size(y_donnees_bruitees, 1), 1)';
    A=A';

    p = probas_classe;
    B = p.*y_donnees_bruitees;
    X = (p.*A) \ B;

    a_Dyx=X(1);
    b_Dyx=X(2);

end