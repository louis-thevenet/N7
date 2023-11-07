%*********************************************************************************************
% Fichier  ~gergaud/ENS//Users/gergaud/ENS/Optim1a/TP-optim/TP-diff-finies/C14_diff_finies.m *
% Décembre 2017                                                                              *
% Université de Toulouse, INP-ENSEEIHT                                                       *
%*********************************************************************************************
%
%
% ======================================================================
% Ce programme estime les paramètres dans le problème d'estimation 
% des paramètres pour le problème de la datation par le carbonne 14
% Programme MATLAB
% Le modèle est:
% A(t)=A0exp(-lambda t)
% On cherche beta = (A0,lambda) de façon à ce que le modèle 
% approche le mieux les données au sens des moindres carrés
% Les programmes et algorithmes utilisés pour la minimisation sont:
% Gauss-Newton et leastsq
% =======================================================================
%
clear all; close all; format shorte
% Initialisation
%
diary res_C14_diff_finies.txt
% Données:


Ti=[500 1000 2000 3000 4000 5000 6300];
Ai=[14.5 13.5 12.0 10.8 9.9 8.9 8.0];
% Visualisation dans IR^3 de la fonction f à minimiser
xmin=9;
xmax=20;
nx=100;
pasx=(xmax-xmin)/nx;
ymin=0;
% ymin=-0.0001;
ymax=0.0003;
ny=100;
pasy=(ymax-ymin)/ny;

x=xmin:pasx:xmax;
y=ymin:pasy:ymax;
[X,Y]=meshgrid(x,y);
[m,n]=size(X);
for i=1:m,
   for j=1:n,
      Z(i,j)=fun_ref(@(beta) res_C14_ref(beta,Ti,Ai),[X(i,j),Y(i,j)]);
   end;
end;
figure(1)
mesh(X,Y,Z)
xlabel('A_0');
ylabel('\lambda')
zlabel('f(A_0,\lambda')

% Visualisation des données et des courbes de niveaux

figure(2) 
subplot(1,2,1)            % Données
hold on;
plot(Ti,Ai,'o')
rect=[0 7000 0 18];       % dimensions des axes
axis(rect)
subplot(1,2,2)            % Courbes de niveaux
hold on
contour(X,Y,Z,50);
xlabel('A_0')
ylabel('\lambda')
hold on
%
% Gauss-Newton
% ------------
% Point de départ
beta0 = [10 0.0001]';   % Newton, fminunc et leastsq converge
% beta0=[15 0.001]'   % Newton, fminunc et leastsq divergent
%beta0=[15 0.0005]'     % Newton diverge, fminu et leastsq convergent
%beta0=[10 0.0005]'
True_Jacobienne = false; % false : approximation par différence finies
% Liste pour le choix de la méthode de différences
list_diff_finies = {'avants','centrees'};
%%%%% MODIFIER LE NUMERO APRES AVOIR CODE LA FONCTION ASSOCIEE DANS LE FICHIER ASSOCIE %%%%%%%%%%%
methode_finite_diff = list_diff_finies{1};


% On trace la courbe de départ
T = linspace(0,6300,100);
A = beta0(1)*exp(-beta0(2)*T);
figure(2)
subplot(1,2,1)
plot(T,A)
figure(2)
subplot(1,2,2)
text(beta0(1),beta0(2),'o point de depart')
% pause
% 
disp('Algorithme de Gauss-Newton')
if ~True_Jacobienne
	ndigits = 9; % précision ndigits
	fprintf("ndigits %d \n", ndigits)
end
disp( strcat('Vraie Jacobienne = ' , sprintf(' %d', True_Jacobienne) ) )
disp( strcat('Methode diff finies = ' +  string(methode_finite_diff)) ) ;

disp('------------------------------------------------------------------')
disp('         k     ||f''(beta)||   f(beta)      ||s||       exitflag ')
disp('------------------------------------------------------------------')

if True_Jacobienne
	Jres = J_res_C14_ref(beta0, Ti);
else
	switch methode_finite_diff
		case 'avants'
	    Jres = diff_finies_avant( @(beta) res_C14_ref(beta,Ti,Ai), beta0, ndigits);
	
        case 'centrees'
	     Jres = diff_finies_centree( @(beta) res_C14_ref(beta,Ti,Ai), beta0, ndigits);
	end
end

res = res_C14_ref(beta0,Ti,Ai);
gradf_beta = norm(Jres'*res);
f_beta = fun_ref(@(beta) res_C14_ref(beta,Ti,Ai), beta0);
disp([0 gradf_beta f_beta]);
Beta = [beta0];

for i=1:10
  option = [sqrt(eps) 1.e-12 i];
  if True_Jacobienne
  [beta, norm_gradf_beta, f_beta, res, norms, k, exitflag] = GN_ref(@(beta) res_C14_ref(beta,Ti,Ai), ...
        @(beta) J_res_C14_ref( beta, Ti), beta0, option);
  else
  switch methode_finite_diff
		case 'avants'
  [beta, norm_gradf_beta, f_beta, res, norms, k, exitflag] = GN_ref(@(beta) res_C14_ref(beta,Ti,Ai), ...
        @(beta) diff_finies_avant(@(beta) res_C14_ref(beta,Ti,Ai), beta, ndigits), beta0, option); 
        case 'centrees'
  [beta, norm_gradf_beta, f_beta, res, norms, k, exitflag] = GN_ref(@(beta) res_C14_ref(beta,Ti,Ai), ...
        @(beta) diff_finies_centree(@(beta) res_C14_ref(beta,Ti,Ai), beta, ndigits), beta0, option); 
  end
  end
  Beta = [Beta beta];
  disp([k norm_gradf_beta f_beta norms exitflag])
% Visualisation
  A=beta(1)*exp(-beta(2)*T);
  subplot(1,2,1)
  plot(T,A)
%  eval(['print -depsc fig_GN_courbe' int2str(i) '_C14'])
  subplot(1,2,2)
  plot(beta(1),beta(2),'o')
end
disp('------------------------------------------------------------------')
disp('betak')
disp(Beta);
figure(1)

print -depsc C14_fig_Gauss_Newton1
figure(2)

print -depsc C14_fig_Gauss_Newton2
diary


% ======================================================================
% Calcul de la fonction à minimiser
% =======================================================================
function sce=fun_ref(res,beta)
% Input:
% ------
% res : fonction résidus
%       res : \IR^p --> \IR^n
% beta : vecteur des paramètres
%        real(p)
%
% Output:
% -------
% sce : (1/2)||res(beta)||^2
%       real
%
% Calcul des résidus
res = res(beta);
res = res(:);
sce=0.5*res'*res;
end
%
% ======================================================================
% "résidus" pour le probleme de datation par le carbonne 14
% =======================================================================
%
%
function r=res_C14_ref(beta,Ti,Ai)
% Calcul des résidus
%
r=Ai-beta(1)*exp(-beta(2)*Ti);
r=r(:);
end
%
% ======================================================================
% Cette fonction calcule la derivee de la fonction residu pour l'exemple
% datation par le carbonne 14
% =======================================================================
%
%
function J_res=J_res_C14_ref(beta,Ti)
%
%
Ti = Ti(:); 
J_res = [-exp(-beta(2)*Ti) (beta(1)*exp(-beta(2)*Ti)).*Ti];
end



