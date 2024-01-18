function L = laplacian(nu,dx1,dx2,N1,N2)
%
%  Cette fonction construit la matrice de l'opérateur Laplacien 2D anisotrope
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
%  L      : Matrice de l'opérateur Laplacien (dimension N1N2 x N1N2)
%
% 

% Initialisation
L=sparse([]);
alpha = 2*nu(1)/(dx1*dx1) + 2*nu(2)/(dx2*dx2);
beta = -nu(2)/(dx2*dx2);
gamma = nu(1)/(dx1*dx1);

tri = zeros(N2, 3);
tri(:, 1) = repmat(beta, N2, 1);
tri(end, 1)=0;
tri(:, 2) = repmat(alpha, N2, 1);
tri(:, 3) = repmat(beta, N2, 1);
tri(end, 3)=0;

L=spdiags(repmat(tri, N1*N2), -1:1, N1*N2, N1*N2);

L = L + spdiags([gamma*ones(N1*N2), gamma*ones(N1*N2)], [-N2, N2], N1*N2, N1*N2);
L=full(L)
end    
