% Auteur : J. Gergaud
% décembre 2017
% -----------------------------
% 



function Jac= diff_finies_centree(fun, x, option)
%
% Cette fonction calcule les différences finies centrées sur un schéma
% Paramètres en entrées
% fun : fonction dont on cherche à calculer la matrice jacobienne
%       fonction de IR^n à valeurs dans IR^m
% x   : point où l'on veut calculer la matrice jacobienne
% option : précision du calcul de fun (ndigits)
%
% Paramètre en sortie
% Jac : Matrice jacobienne approximé par les différences finies
%        real(m,n)
% ------------------------------------
    w = max(power(10, -16), power(10, -option(1)));
    h = power(w, 1/3) * max(ones(size(x, 1)), abs(x))  .*sgn(x);
    I = eye(size(x, 1), 1);
    for i=1:size(x, 1)
        Jac(:, i) = (fun(x+h .* I) - fun(x-h .* I) ) ./ (2*h(i));
    end
end

function s = sgn(x)
% fonction signe qui renvoie 1 si x = 0
if x==0
  s = 1;
else 
  s = sign(x);
end
end





