function nbfig_out=plot_uh(uh,dx1,dx2,N1,N2,nbfig)
 %
%  Cette fonction affiche la solution de l'EDP
%
%  Inputs
%  ------
%
%  uh : solution numérique de l'EDP. 
%
%  dx1 : pas d'espace dans la direction x1.
%
%  dx2 : pas d'espace dans la direction x2.
%
%  N1 : nombre de points de grille dans la direction x1.
%
%  N2 : nombre de points de grilles dans la direction x2.
%
%  nbfig : identifiant de la figure
%
%  Outputs:
%  -------
%
%  nbfig_out : identifiant de la figure
%
 
  
  % Construction de la grille pour l'affichage.
  x1min=0.;
  x1max=dx1*(N1+1);
  x2min=0.;
  x2max=dx2*(N2+1);
  if(x1max==0)
    disp('Erreur : L1=0')
    return
  else  
    rxy=x2max/x1max;
  end
  
  x1=x1min:dx1:x1max;
  x2=x2min:dx2:x2max;
  [X,Y]=meshgrid(x1,x2);
  [m,n]=size(X);
  
  % Mise au format 2D de la solution.  
  Z=zeros(N2+2,N1+2);
  Z(2:N2+1,2:N1+1)=reshape(uh,N2,N1);
 
  % Affichage
  nbfig_out=nbfig;
  figure(nbfig_out)                          
  s=surf(X,Y,Z,'FaceAlpha',0.5);
  s.EdgeColor='none';
  pbaspect([1 rxy 1]);
  colorbar;
  xlabel('x_1')
  ylabel('x_2')
  zlabel('u')
  
end
