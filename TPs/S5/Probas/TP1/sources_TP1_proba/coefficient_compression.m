% Fonction coefficient_compression (exercice_2.m)

function coeff_comp = coefficient_compression(signal_non_encode,signal_encode)
    coeff_comp = 8*size(signal_non_encode,1) / size(signal_encode, 1);
end