%****************************************************************************************************
% Fichier  ~gergaud/ENS//Users/gergaud/ENS/Optim1a/TP-optim/TP-diff-finies/exem1_diff_finies_ref.m *
% Décembre 2017                                                                                     *
% Université de Toulouse, INP-ENSEEIHT                                                              *
%****************************************************************************************************
%
%
% ======================================================================
% Ce programma résout par l'algorithme de Gauss-Newton le problème 
% d'optimisation
% Min f(x) = (1/2)((x_1^2-x_2)^2+(1-x_1)^2)=(1/2)||r(x)||^2
% =======================================================================
%



clear all; close all; format shorte
diary res_exem1_diff_finies.txt





% Initialisation
%
% Visualisation dans IR^3 de la fonction f à minimiser
xmin=-1;
xmax=2;
nx=100;
pasx=(xmax-xmin)/nx;
ymin=-1;
% ymin=-0.0001;
ymax=4;
ny=100;
pasy=(ymax-ymin)/ny;
x=xmin:pasx:xmax;
y=ymin:pasy:ymax;
[X,Y]=meshgrid(x,y);
[m,n]=size(X);
for i=1:m
   for j=1:n
      Z(i,j)=fun_ref([X(i,j),Y(i,j)]);
   end
end
figure(1)
mesh(X,Y,Z)
xlabel('x_1');
ylabel('x_2')
zlabel('f(x)')

% Visualisation des données et des courbes de niveaux

figure(2)  % Courbes de niveaux

hold on
contour(X,Y,Z,50);
xlabel('x_1')
ylabel('x_2')
hold on
%
% Gauss-Newton
% ------------
% Point de départ
beta0 = [500 100]';   
text(beta0(1),beta0(2),'o point de depart')
True_Jacobienne = false; % false : approximation par différence finies
% Liste pour le choix de la méthode de différences
list_diff_finies = {'avants','centrees'};
%%%%% MODIFIER LE NUMERO APRES AVOIR CODE LA FONCTION ASSOCIEE DANS LE FICHIER ASSOCIE %%%%%%%%%%%
methode_finite_diff = list_diff_finies{1};



disp('Algorithme de Gauss-Newton')
disp( strcat('Vraie Jacobienne =' , sprintf('%d', True_Jacobienne) ) );
disp( strcat('Methode diff finies = ' +  string(methode_finite_diff)) ) ;

if ~True_Jacobienne 
	ndigits = 8; % précision ndigits
	fprintf("ndigits :  %d \n", ndigits)
end

disp('------------------------------------------------------------------')
disp('         k     ||f''(beta)||   f(beta)      ||delta||    exitflag ')
disp('------------------------------------------------------------------')

if True_Jacobienne
	Jres = J_res1(beta0);
else
	switch methode_finite_diff
		case 'avants'
	    Jres = diff_finies_avant(@res1,beta0, ndigits);
        case 'centrees'
	     Jres = diff_finies_centree(@res1,beta0, ndigits);
	end
end

res = res1(beta0);
gradf_beta = norm(Jres'*res);
f_beta = fun_ref(beta0);
disp([0 gradf_beta f_beta]);
Beta = [beta0];
for i=1:2
  option = [sqrt(eps) 1.e-12 i];
  if True_Jacobienne
     [beta, norm_gradf_beta, f_beta, res, norms, k, exitflag] = GN_ref(@res1, @J_res1, beta0, option); 
  else
     
  switch methode_finite_diff
		case 'avants'
	   [beta, norm_gradf_beta, f_beta, res, norms, k, exitflag] = GN_ref(@res1, @(beta) diff_finies_avant(@res1,beta,ndigits), beta0, option); 
      case 'centrees' 
	     [beta, norm_gradf_beta, f_beta, res, norms, k, exitflag] = GN_ref(@res1, @(beta) diff_finies_centree(@res1,beta,ndigits), beta0, option); 
  end
end
  Beta = [Beta beta];
  disp([k norm_gradf_beta f_beta norms exitflag])
% Visualisation
  plot(beta(1),beta(2),'o')
end
disp('------------------------------------------------------------------')
disp('betak')
disp(Beta);
figure(1)
print -depsc  exem_1_fig_GN1_exem1
figure(2)
print -depsc exem_1fig_GN2_exem1
diary


% ======================================================================
% Calcul de la fonction à minimiser
% =======================================================================



% ======================================================================
% "résidus" pour le probleme:
% Min f(x)=0.5*((x_1^2-x_2)^2+(1-x_1)^2)
% =======================================================================
%
%
function r=res1(x)
r=[x(1)^2-x(2)
   1-x(1)];
end


% ======================================================================
% Calcul de la fonction objective à minimiser
% Min f(x)=0.5*((x_1^2-x_2)^2+(1-x_1)^2)
% =======================================================================
%
%
function sce=fun_ref(x)
r=[x(1)^2-x(2)
   1-x(1)];
   sce = 0.5*r'*r;
end

% ========================================================================
% Cette fonction calcule la derivee de la fonction residu pour l'exemple 1
% ========================================================================
%
%
function J_res=J_res1(x)
%
% 
J_res = [2*x(1) -1 ; -1 0];
end



