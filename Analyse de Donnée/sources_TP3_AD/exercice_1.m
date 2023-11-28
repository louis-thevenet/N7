clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);
azimuth = -30;
elevation = 40;

% Choix de la paire de caracteristiques la plus discriminante (a modifier !) :
load donnees_carac;
noms_carac = {'Compacite','Contraste','Texture'};
ind_carac_1 = 1;
ind_carac_2 = 2;
nom_carac_1 = noms_carac{ind_carac_1};
nom_carac_2 = noms_carac{ind_carac_2};

% Recuperation des colonnes de X correspondant aux deux caracteristiques choisies de l'ensemble d'apprentissage :
X_app = X_app(:,[ind_carac_1 ind_carac_2]);
nb_donnees_app = size(Y_app,1);

% Maillage pour l'affichage des vraisemblances des 2 classes :
pas = 0.002;
marge = 0.005;
graduation_carac_1 = min(X_app(:,1))-marge:pas:max(X_app(:,1))+marge;
graduation_carac_2 = min(X_app(:,2))-marge:pas:max(X_app(:,2))+marge;
limites_affichage = [graduation_carac_1(1) graduation_carac_1(end) graduation_carac_2(1) graduation_carac_2(end)];

%------------------------------------------------------------------------------------------

% Calcul des parametres et du modele de la vraisemblance pour la classe 1 (fibromes) :
num_classe = 1;
[mu_1,Sigma_1] = estim_param_vraisemblance(X_app(Y_app == num_classe,:)); % FONCTION A CODER
[grille_carac1,grille_carac2] = meshgrid(graduation_carac_1,graduation_carac_2);
X_grille = [grille_carac1(:),grille_carac2(:)];
modele_V_fibrome = modelisation_vraisemblance(X_grille,mu_1,Sigma_1); % FONCTION A CODER
modele_V_fibrome = reshape(modele_V_fibrome,length(graduation_carac_2),length(graduation_carac_1));

% Affichage des donnees d'apprentissage et de la vraisemblance de la classe 1 (fibromes) :
nb_fibrome = sum(Y_app == num_classe);
figure('Name',['Vraisemblance de la classe ' num2str(num_classe)],...
       'Position',[0.02*L,0.1*H,0.31*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    dc1 = plot3(X_app(Y_app == num_classe,1),X_app(Y_app == num_classe,2),zeros(nb_fibrome,1), ...
                'bx','MarkerSize',10,'LineWidth',2);
    hold on;
    mc1 = surface(graduation_carac_1,graduation_carac_2,modele_V_fibrome, ...
                  'EdgeColor',[0.5 0.5 1],'FaceColor','none');
    view(azimuth,elevation);
    axis(limites_affichage);
    grid on;

    title(['Classe ' num2str(num_classe) ' : fibromes']);
    xlabel(nom_carac_1);
    ylabel(nom_carac_2);
    legend([dc1, mc1],'Dermatofibromes',['Modele de la classe ' num2str(num_classe)], ...
           'Location','Best','FontSize',15);
    zlabel('Vraisemblance','Rotation',90);
    set(gca,'FontSize',20);
    
%------------------------------------------------------------------------------------------
    
% Calcul des parametres et du modele de la vraisemblance pour la classe 2 (melanomes) :
num_classe = 2;
[mu_2,Sigma_2] = estim_param_vraisemblance(X_app(Y_app == num_classe,:)); % FONCTION A CODER
[grille_carac1,grille_carac2] = meshgrid(graduation_carac_1,graduation_carac_2);
modele_V_melanome = modelisation_vraisemblance([grille_carac1(:),grille_carac2(:)],mu_2,Sigma_2); % FONCTION A CODER
modele_V_melanome = reshape(modele_V_melanome,length(graduation_carac_2),length(graduation_carac_1));

% Affichage des donnees d'apprentissage de la classe "2" (melanomes) :
nb_melanome = sum(Y_app == num_classe);
figure('Name',['Vraisemblance de la classe ' num2str(num_classe)],...
       'Position',[0.34*L,0.1*H,0.31*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    dc2 = plot3(X_app(Y_app == num_classe,1),X_app(Y_app == num_classe,2),zeros(nb_melanome,1),...
                'ro','MarkerSize',10,'LineWidth',2);
    hold on;
    mc2 = surface(graduation_carac_1,graduation_carac_2,modele_V_melanome,...
                  'EdgeColor',[1 0.5 0.5],'FaceColor','none');
    view(azimuth,elevation);
    axis(limites_affichage);
    grid on;

    title(['Classe ' num2str(num_classe) ' : melanomes']);
    xlabel(nom_carac_1);
    ylabel(nom_carac_2);
    legend([dc2, mc2],'Melanomes',['Modele de la classe ' num2str(num_classe)],'Location',...
           'Best','FontSize',15);
    zlabel('Vraisemblance','Rotation',90);
    set(gca,'FontSize',20);
    
%------------------------------------------------------------------------------------------

% Superposition des 2 vraisemblances :
figure('Name','Superposition des deux vraisemblances',...
       'Position',[0.66*L,0.1*H,0.31*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
    surface(graduation_carac_1,graduation_carac_2,modele_V_fibrome,...
            'EdgeColor',[0.5 0.5 1],'FaceColor','none');
    hold on;
    surface(graduation_carac_1,graduation_carac_2,modele_V_melanome,...
            'EdgeColor',[1 0.5 0.5],'FaceColor','none');
    view(azimuth,20);
    axis(limites_affichage);
    grid on;

    title('Superposition des deux classes');
    xlabel(nom_carac_1);
    ylabel(nom_carac_2);
    legend('Modele de la classe 1','Modele de la classe 2','Location','Best','FontSize',15);
    zlabel('Vraisemblance','Rotation',90);
    set(gca,'FontSize',20);

% Orientation de la figure pour obtenir les zones de choix entre les classes
elevation = 21:90;
azimuth = linspace(azimuth,0,length(elevation));
    for k = 1:length(elevation)
        view(azimuth(k),elevation(k));
        drawnow;
    end
    
save donnees_exercice_1;                    
