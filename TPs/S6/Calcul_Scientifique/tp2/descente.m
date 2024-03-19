%--------------------------------------------------------------------------
% ENSEEIHT - 1SN - Calcul scientifique
% TP2 - Factorisation LU
% descente.m
%---------------------------------------------------------------------------

function x = descente(L,p,b)
%---------------------------------------------------------------------------
% Resoudre L x = Pb avec 
% L triangulaire inferieure avec diagonale de 1, b second membre,
% et p vecteur des indices de permutation des lignes.
%---------------------------------------------------------------------------
       
     %Initialisation
     [n, ~] = size(L);
     x=b;

      for j=1:n 
        for i=1:j-1
            x(j) = x(j) - L(j,i) * x(i);
        end
        %x(j) = x(j) / L(j,j);
        
     end
     
end
