% Fonction vectorisation_par_colonne (exercice_1.m)

function [Vg,Vd] = vectorisation_par_colonne(I)
    Vd = I(:,2:end);
    Vd = Vd(:);
    Vg = I(:,1:end-1);
    Vg = Vg(:);
end