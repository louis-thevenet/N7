% fonction estim_param_SVM_noyau (pour l'exercice 2)

function [X_VS,Y_VS,Alpha_VS,c,code_retour] = estim_param_SVM_noyau(X,Y,sigma)
n=size(X,1);
G = ones(n,1);
for i = 1:n
    for j=1:n
        G(i,j) = exp(-(norm(X(i)-X(j))*norm(X(i)-X(j)) / (sigma*sigma*2)));
    end
end

A = [];
b = [];
Aeq = Y';
beq = 0;
[alpha,~,code_retour] = quadprog(G, -ones(n, 1),A,b,Aeq, beq, zeros(n,1), []);




X_VS = X(alpha > 1e-6, :);
Y_VS = Y(alpha > 1e-6);
alpha_VS = alpha(alpha > 1e-6);


  c=G(1, :) * diag(Y_VS)* alpha_VS - Y_VS(1);



end
