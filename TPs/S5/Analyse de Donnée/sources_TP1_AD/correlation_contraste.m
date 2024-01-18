% function correlation_contraste (pour exercice_1.m)

function [correlation,contraste] = correlation_contraste(X)
    X_c = X-mean(X);
    Sigma =  (X_c' * X_c)/size(X, 1);

    r_1_2 = Sigma(1, 2)/sqrt(Sigma(1, 1)*Sigma(2,2))    ;
    r_1_3 = Sigma(1, 3)/sqrt(Sigma(1, 1)*Sigma(3,3));
    r_2_3 = Sigma(2, 3)/sqrt(Sigma(2,2)*Sigma(3,3));

    correlation = [r_1_2, r_1_3, r_2_3];
    denom = Sigma(1,1)*Sigma(1,1) + Sigma(2,2)*Sigma(2,2) + Sigma(3,3)*Sigma(3,3);
    
    contraste = [
        Sigma(1,1)*Sigma(1,1);
        Sigma(2,2)*Sigma(2,2);
        Sigma(3,3)*Sigma(3,3)
        ] / denom;
end
