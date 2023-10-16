% Fonction histogramme_normalise (exercice_2.m)

function [vecteur_Imin_a_Imax,vecteurs_frequences] = histogramme_normalise(I)

    vecteur_Imin_a_Imax = min(I(:)):1:max(I(:));
    h=histcounts(I, [vecteur_Imin_a_Imax,max(I(:))+1]);
    vecteurs_frequences = h / sum(h);

end