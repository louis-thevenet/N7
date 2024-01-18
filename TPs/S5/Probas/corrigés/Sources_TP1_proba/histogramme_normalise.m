% Fonction histogramme_normalise (exercice_2.m)

function [vecteurs_frequences,vecteur_Imin_a_Imax] = histogramme_normalise(I)
    I = I(:);
    vecteur_Imin_a_Imax = min(I):max(I)+1;
    vecteurs_frequences = histcounts(I,vecteur_Imin_a_Imax) ./ size(I,1);
    vecteur_Imin_a_Imax = vecteur_Imin_a_Imax(1:end-1);
end