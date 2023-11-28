% fonction modelisation_vraisemblance (pour l'exercice 1)

function modele_V = modelisation_vraisemblance(X,mu,Sigma)

    denom = sqrt(2 * pi * det(Sigma));
    InvSigma = inv(Sigma);
    for i=1:size(X, 1)

        modele_V(i) = exp((-1/2) * ((X(i, :)-mu)*InvSigma*(X(i, :)-mu)')) / denom;
    end
    
    
    

end