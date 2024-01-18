% Fonction vectorisation_par_colonne (exercice_1.m)

function [Vg,Vd] = vectorisation_par_colonne(I)

    Vg = I(:, 1:(end-1));
    Vd = I(:, 2:end);
    Vg=Vg(:);
    Vd=Vd(:);
end