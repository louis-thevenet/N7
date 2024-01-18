% Fonction reconstruction_image (exercice_3.m)

function I_reconstruite = reconstruction_image(I_encodee,dictionnaire,hauteur_I,largeur_I)
    I_reconstruite = reshape(huffmandeco(I_encodee,dictionnaire), hauteur_I, largeur_I);
    I_reconstruite(:, 2:end) = I_reconstruite(:, 2:end) + I_reconstruite(:, 1:(end-1));
end