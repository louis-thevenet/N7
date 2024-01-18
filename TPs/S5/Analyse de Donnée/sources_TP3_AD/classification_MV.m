% fonction classification_MV (pour l'exercice 2)

function Y_pred_MV = classification_MV(X,mu_1,Sigma_1,mu_2,Sigma_2)
    Y_pred_MV = zeros(size(X, 1), 1);
    for i=1:size(X,1)
        if modelisation_vraisemblance(X(i, :), mu_1, Sigma_1) > modelisation_vraisemblance(X(i, :), mu_2, Sigma_2)
            Y_pred_MV(i)=1;
        else
            Y_pred_MV(i)=2;
        end
    end

    
end
        