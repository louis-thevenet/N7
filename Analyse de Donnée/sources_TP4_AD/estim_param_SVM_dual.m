% fonction estim_param_SVM_dual (pour l'exercice 1)

function [X_VS,w,c,code_retour] = estim_param_SVM_dual(X,Y)
n = size(X, 1);
H = diag(Y)*(X*X')*diag(Y);
A = [];
b = [];
Aeq = ones(n,1)';
beq = 1;
[alpha,~,code_retour] = quadprog(H, -ones(n, 1),A,b,Aeq, beq, zeros(n,1), []);


w = X' * diag(Y)* alpha;


X_VS = (alpha > 1e-6).*X;
X_VS(X_VS>1e-6)=[];

c=w'*X(1)-Y(1);
end
