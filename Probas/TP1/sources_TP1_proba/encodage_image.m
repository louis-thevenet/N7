% Fonction encodage_image (exercice_2.m)

function [I_encodee,dictionnaire,hauteur_I,largeur_I] = encodage_image(I)
    [vecteur_Imin_a_Imax,vecteurs_frequences] = histogramme_normalise(I); % FONCTION A CODER
    
    dictionnaire = huffmandict(vecteur_Imin_a_Imax,vecteurs_frequences);
    I_encodee = huffmanenco(I(:),dictionnaire)
    hauteur_I = size(I,1);
    largeur_I=size(I,2);
end