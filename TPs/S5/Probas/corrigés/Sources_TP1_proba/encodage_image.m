% Fonction encodage_image (exercice_2.m)

function [I_encodee,dictionnaire,hauteur,largeur] = encodage_image(I)
    [vecteurs_frequences,vecteur_Imin_a_Imax] = histogramme_normalise(I);

    dictionnaire = huffmandict(vecteur_Imin_a_Imax,vecteurs_frequences);
    I_encodee = huffmanenco(I(:),dictionnaire);
    [hauteur, largeur] = size(I);
end