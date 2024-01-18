% fonction classification_MAP (pour l'exercice 3)

function Y_pred_MAP = classification_MAP(X,p1,mu_1,Sigma_1,mu_2,Sigma_2)

    Y_pred_MV = zeros(size(X, 1), 1);
    for i=1:size(X,1)
        if p1*modelisation_vraisemblance(X(i, :), mu_1, Sigma_1) > modelisation_vraisemblance(X(i, :), mu_2, Sigma_2)*(1-p1)
            Y_pred_MV(i)=1;
        else
            Y_pred_MV(i)=2;
        end
    end
    
end
