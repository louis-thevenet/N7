% function ACP (pour exercice_2.m)

function [C,bornes_C,coefficients_RVG2gris] = ACP(X)
    X_c = X-mean(X);
    Sigma =  (X_c' * X_c)/size(X, 1);
    [W, D] = eig(Sigma);
    [~, I] = sort(diag(D), "descend");

    W = W(:, I);
    
    C = X_c * W;


    bornes_C = [min(C), max(C)];
    coefficients_RVG2gris=normalize(W(:, 1));
end
