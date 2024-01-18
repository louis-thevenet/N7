% fonction classification_SVM_avec_noyau (pour l'exercice 2)

function Y_pred = classification_SVM_avec_noyau(X,sigma,X_VS,Y_VS,Alpha_VS,c)

n=size(X,1);
G = ones(n,1);
for i = 1:n
    for j=1:n
        G(i,j) = exp(-(norm(X(i)-X(j))*norm(X(i)-X(j)) / (sigma*sigma*2)));
    end
end

Y_pred = sign(G * diag(Y_VS) * Alpha_VS - c);

end