% Auteur : Joseph Gergaud, INP-ENSEEIHT & IRIT
% Date   : décembre 2017
%
% Test de l'algorithme de différences finies avant sur la fonction cosinus
% fun1(x) = cos(x)
% fun2(x) = cos(x) + alpha*rand(1)
% Avec 2 points différents
%

% On réinitialise l'environnement
%
clear;
close all;
clc;

% Des paramètres pour l'affichage
%
tirets  = '------------------------------------------';
LW      = 1.5;
set(0,'defaultaxesfontsize'           ,  14     , ...
      'DefaultTextVerticalAlignment'  , 'bottom', ...
      'DefaultTextHorizontalAlignment', 'left'  , ...
      'DefaultTextFontSize'           ,  12     , ...
      'DefaultFigureWindowStyle'      ,'docked');

% On choisit un format long pour plus de détails sur les résultats numériques
%
format shortE;

% Exercice 2.2
%-------------------------------------------------------------------------------------------------------------
% Test de l'algorithme de différences finies avant sur la fonction cosinus
%
disp(tirets);
disp('Test de l''algorithme de différences finies  sur la fonction cosinus');

% Les differentes fonctions et la jacobienne theorique
fun1 = @(x) -cos(x);
fun2 = @(x) -cos(x) + 1.e-8*rand(1);
true_jac = @(x)  sin(x);

% Variables pour le choix de la methode de difference finie
list_diff_finies = {'avants','centrees','complexes'};
%%%%% MODIFIER LE NUMERO APRES AVOIR CODE LA FONCTION ASSOCIEE %%%%%%%%%%%
methode_finite_diff = list_diff_finies{1};

% Calcul de l'erreur sur la fonction dans le cas bruité et non bruité
omega_true_fun = eps((1));
omega_per_fun = 1e-8;



% Estimation du h* en fonction de la difference finie choisie
switch methode_finite_diff
	case 'avants'
        h_star_true_fun = sqrt(omega_true_fun);
        h_star_per_fun = sqrt(omega_per_fun);
    case 'centrees'
        h_star_true_fun = omega_true_fun^(1/3.);
        h_star_per_fun = omega_per_fun^(1/3.);
    otherwise
        h_star_true_fun = sqrt(omega_true_fun);
        h_star_per_fun = sqrt(omega_true_fun);
end


 


% Points ou l'on souhaite effectuer les tests
x0 = pi/3;
x1 = 1.e6*pi/3;

% Ordres pour faire les tests (16 + celui de h*)
ordrestrue = ([1:floor(-log10(h_star_true_fun)), -log10(h_star_true_fun), ceil(-log10(h_star_true_fun)):16]);
ordresper = ([1:floor(-log10(h_star_per_fun)), -log10(h_star_per_fun), ceil(-log10(h_star_per_fun)):16]);
% Initialisation des vecteurs d'erreur

err_x0 = zeros(1,length(ordrestrue)); 
err_x0p = zeros(1,length(ordresper));
err_x1 = zeros(1,length(ordrestrue));

% Définition du schéma à employer


switch methode_finite_diff
    % Differences finies avant 
    case 'avants'
        diff_finies = @(fun,x,h) forwardfiniteDiff(fun,x,h);
    % Differences finies avant        
    case 'centrees'
        diff_finies = @(fun,x,h) centredfiniteDiff(fun,x,h);
    % Differences finies avant 
    case 'complexes'
        diff_finies = @(fun,x,h) derivee_complexe(fun,x,h);
end

for i = 1:length(ordrestrue)
    h = 10^(-ordrestrue(i));
    err_x0(i)  = abs(diff_finies(fun1,x0,h) - (true_jac(x0)));
    err_x1(i)  = abs(diff_finies(fun1,x1,h) - (true_jac(x1)));
    
    h = 10^(-ordresper(i));
    err_x0p(i) = abs(diff_finies(fun2,x0,h) - (true_jac(x0)));
    
    
end

% Affichage de la courbe pour x0
affichage_erreur(ordrestrue, err_x0, h_star_true_fun, 'x0',   methode_finite_diff, LW);

% Affichage de la courbe pour x1
affichage_erreur(ordrestrue, err_x1, h_star_true_fun, 'x1',   methode_finite_diff, LW);
% Affichage de la courbe pour x0p
affichage_erreur(ordresper, err_x0p, h_star_per_fun, 'x0p', methode_finite_diff, LW);
    





% Fonctions ---------------------------------------------------------------

function affichage_erreur(ordres,err,h_star,x_str,methode_str,LW)
    figure;
        non_nul_element = find(err);
        err = err(non_nul_element);
        ordres = ordres(non_nul_element);
        % Courbe des erreurs pour les differents ordres en bleu
        loglog(10.^(-ordres), err, 'b', 'LineWidth', LW);
        hold on;
        % Ligne verticale pour situer le pas optimale h* en rouge
        line([h_star, h_star], [min(err), max(err)], 'Color', 'r');
        grid on; 
        xlabel('h'); 
        ylabel('erreurs');
        
        titre = ['Erreur des differences finies ' methode_str];
        
      
        
        switch x_str
            case 'x0'
                titre = [titre, sprintf('\n sur la fonction cosinus en x_0= %s/3', '\pi')];
            case 'x1'
                titre = [titre, sprintf('\n sur la fonction cosinus en x_1= %s/3', '1.e6*\pi')];
            case 'x0p'
                titre = [titre, sprintf('\n sur la fonction cosinus perturbee en x_0= %s/3', '\pi')];
        end
        
        title(titre, 'HorizontalAlignment', 'center');
        legend({'Numerique','Optimal'},'Location','SouthWest');
        grid on;
        drawnow;
        % Enregistrement de l'image
        print(['fig_diff_finies_'  x_str],'-dpng'); 
end


function Jac = forwardfiniteDiff(fun,x,h)
%
% Cette fonction calcule les différences finies
% Paramètres en entrées
% fun : fonction dont on cherche à calculer la matrice jacobienne
%       fonction de IR^n à valeurs dans IR^m
% x   : point où l'on veut calculer la matrice jacobienne
% h   : pas
%
% Paramètre en sortie
% Jac : Matrice jacobienne approximé par les différences finies
%        real(m,n)
% ------------------------------------
Jac = 0;
end

function Jac = centredfiniteDiff(fun, x, h)
%
%Cette fonction calcule les différences finies à l'aide d'un schéma centré
%Paramètres en entrées
% fun : fonction dont on cherche à calculer la matrice jacobienne
%       fonction de IR^n à valeurs dans IR^m
% x   : point où l'on veut calculer la matrice jacobienne
% h   : pas
%
% Paramètre en sortie
% Jac : Matrice jacobienne approximé par les différences finies
%        real(m,n)
% ------------------------------------
Jac = 0;
end

function Jac = derivee_complexe(fun, x,h)

%
%Cette fonction calcule les différences finies à l'aide d'un schéma complexe
%Paramètres en entrées
% fun : fonction dont on cherche à calculer la matrice jacobienne
%       fonction de IR^n à valeurs dans IR^m
% x   : point où l'on veut calculer la matrice jacobienne
% h   : pas
%
% Paramètre en sortie
% Jac : Matrice jacobienne approximé par les différences finies
%        real(m,n)
% ------------------------------------
Jac = 0;
end




