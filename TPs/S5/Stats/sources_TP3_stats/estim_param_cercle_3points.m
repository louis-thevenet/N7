% fonction estim_param_cercle_3points

function [C_3p,R_3p] = estim_param_cercle_3points(x,y)

    A = 2*[-x(1)+x(2) -y(1)+y(2) ; ...
           -x(1)+x(3) -y(1)+y(3)];

    B = [-x(1)^2+x(2)^2-y(1)^2+y(2)^2 ; ...
         -x(1)^2+x(3)^2-y(1)^2+y(3)^2];

    C_3p = A\B;
    
    R_3p = sqrt((x(1)-C_3p(1))^2+(y(1)-C_3p(2))^2);

end
