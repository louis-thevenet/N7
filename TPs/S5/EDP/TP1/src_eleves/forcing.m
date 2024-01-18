function b=forcing(nu, dx1, dx2, N1, N2)
%
%  Cette fonction construit le vecteur de forçage de l'EDP
%
%  Inputs
%  ------
%
%  nu : nu=[nu1;nu2], coefficients de diffusivité dans les dierctions x1 et x2. 
%
%  dx1 : pas d'espace dans la direction x1.
%
%  dx2 : pas d'espace dans la direction x2.
%
%  N1 : nombre de points de grille dans la direction x1.
%
%  N2 : nombre de points de grilles dans la direction x2.
%
%  Outputs:
%  -------
%
%  b      : vecteur de forçage (dimension N1N2)
%
% 

% Initialisation
b=zeros(N1*N2,1);
A =laplacian(nu, dx1, dx2,N1, N2);
c = - ones(N1*N2, 1);
b = A\c

end
