% Fonction reconstruction_image (exercice_3.m)

function I_reconstruite = reconstruction_image(I_encodee,dictionnaire,hauteur,largeur)
    I_decodee = huffmandeco(I_encodee,dictionnaire);
    I_reconstruite = reshape(I_decodee,hauteur,largeur);
    I_reconstruite = cumsum(I_reconstruite,2);
end