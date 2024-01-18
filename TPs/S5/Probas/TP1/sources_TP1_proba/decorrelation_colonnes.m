% Fonction decorrelation_colonnes (exercice_2.m) 

function I_decorrelee = decorrelation_colonnes(I)
    
    I_decorrelee = repmat(I, 1);
    I_decorrelee(:, 2:end) = I_decorrelee(:, 2:end) - I(:, 1:(end-1));
end