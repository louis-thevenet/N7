%--------------------------------------------------------------------------
% ENSEEIHT - 1SN - Calcul scientifique
% TP2 - Factorisation LU
% remontee.m
%---------------------------------------------------------------------------

function x = remontee(U,b)
%---------------------------------------------------------------------------
% Resoudre U x = b avec 
% U triangulaire superieure, b second membre.
%---------------------------------------------------------------------------
       
     %Initialisation
     [n, ~] = size(U);
     x=b;
     
     for j=n:-1:1
        for i=j+1:1:n
            x(j) = x(j) - U(j,i) * x(i);
        end
        x(j) = x(j) / U(j,j);
        
     end
   
end
