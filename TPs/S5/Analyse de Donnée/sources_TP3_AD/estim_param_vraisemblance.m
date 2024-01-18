% fonction estim_param_vraisemblance (pour l'exercice 1)

function [mu,Sigma] = estim_param_vraisemblance(X)

   mu=mean(X);
   Sigma = (X-mu)' * (X-mu)/length(X);

end