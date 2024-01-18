% fonction estim_param_SVM_dual (pour l'exercice 1)

function [X_VS,w,c,code_retour] = estim_param_SVM_dual(X,Y)
n = size(X, 1);
H = diag(Y)*(X*X')*diag(Y);
A = [];
b = [];
Aeq = Y';
beq = 0;
[alpha,~,code_retour] = quadprog(H, -ones(n, 1),A,b,Aeq, beq, zeros(n,1), []);




X_VS = X(alpha > 1e-6, :);
Y_VS = Y(alpha > 1e-6);
alpha_VS = alpha(alpha > 1e-6);
w = X_VS' * diag(Y_VS)* alpha_VS;

c=w'*X_VS(1,:)'-Y_VS(1);
end
