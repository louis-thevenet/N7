function [uhref]=diffusivity(nu,L1,L2,N1,N2)
%
%  Cette fonction résoud le problème du calcul d'une solution du Laplacien anisotrope. 
%
%  Inputs
%  ------
%
%  nu: [nu1;nu2] valeurs des paramètres de diffusivité.
%
%  L1 : longeur du domaine dans la direction x1.
%
%  L2 : longueur du domaine dans la direction x2.
%
%  N1 :  nombre de points de grille dans la direction x1.
%
%  N2 :  nombre de points de grille dans la direction x2.
%  
%
%  Outputs:
%  -------
%
%  uhref : vecteur de taille N1*N2 contenant une approximation de la solution
%
% Ajout du repertoire Affichage à l'environnement
  addpath('Affichage');

% Construction de la grille
 dx1 = L1/(N1+1);
 dx2 = L2/(N2+1);

% Calcul de la solution
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
 

   % Calcul de la matrice du systeme

   L = laplacian(nu,dx1,dx2,N1,N2);
   
   % Calcul de l'approximation de la solution de l'EDP
   %%%%%%%%%%%%%%%%%%%%%%%%%%%
   %%%%%%%    TO DO   %%%%%%%%
   %%%%%%%%%%%%%%%%%%%%%%%%%%ù
   uhref=zeros(N1*N2,1);
      
  %Affichage de la solution approximee
  fig_ref = plot_uh(uhref,dx1,dx2,N1,N2,2); drawnow;
  
end
