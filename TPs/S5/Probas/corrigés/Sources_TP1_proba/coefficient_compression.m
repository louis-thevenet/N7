% Fonction coefficient_compression (exercice_2.m)

function coeff_comp = coefficient_compression(signal_non_encode,signal_encode)
    nbpixels_non_encode = size(signal_non_encode(:),1);
    nbpixels_encode = size(signal_encode(:),1);
    coeff_comp = 8 * nbpixels_non_encode / nbpixels_encode;
end