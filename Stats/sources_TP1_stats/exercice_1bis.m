clear
close all
clc

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Creation de la droite et des donnees bruitees :
taille = 20;
bornes = [-taille taille -taille taille];
n = 150;
sigma = 2;
[x_droite,y_droite,x_donnees_bruitees,y_donnees_bruitees, theta_0, rho_0] ...
			         = creation_droite_et_donnees_bruitees(taille,n,sigma);

% Estimation de la droite de regression par le maximum de vraisemblance :
n_tirages = 100;
tirages_psi = tirages_aleatoires_uniformes(n_tirages);
[a_Dyx_MV,b_Dyx_MV,residus_Dyx_MV] = ...
    estim_param_Dyx_MV(x_donnees_bruitees,y_donnees_bruitees,tirages_psi); % FONCTION A CODER

% Calcul de l'ecart angulaire :
theta_Dyx_MV = atan(-1/a_Dyx_MV);
EA_Dyx_MV = abs(theta_Dyx_MV-theta_0);
EA_Dyx_MV = min([EA_Dyx_MV pi-EA_Dyx_MV])/pi*180;

% Affichage de la droite de regression estimee par le maximum de vraisemblance :
figure('Name','Estimation par le maximum de vraisemblance', ...
	   'Position',[0.01*L,0.1*H,0.36*L,0.7*H]);
    x_DYX_MV = [-taille;x_donnees_bruitees;taille];
    y_DYX_MV = a_Dyx_MV*x_DYX_MV+b_Dyx_MV;
    hold on;
    for k = 2:length(x_DYX_MV)-1
        he = plot([x_DYX_MV(k) x_donnees_bruitees(k-1)],[y_DYX_MV(k) y_donnees_bruitees(k-1)], ...
                  'Color',[1 0.6 0.6]);
    end
    hd = plot(x_droite,y_droite,'b-','LineWidth',3);
    hmv = plot(x_DYX_MV,y_DYX_MV,'r','LineWidth',2);
    hdb = plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
    axis equal;
    axis(bornes);
    grid on
    
    title(['Ecart angulaire MV = ' num2str(EA_Dyx_MV,'%.2f') '°'])
    lg = legend([hd, hdb, hmv, he], ...
                '~Droite', ...
                '~Donnees bruitees', ...
                '~$D_{YX}$ (maximum de vraisemblance)', ...
                '~Erreurs residuelles', ...
                'Location','SouthWest');
    set(lg,'Interpreter','Latex');
    hx = xlabel('$x$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',15);

% Affichage des erreurs residuelles :
figure('Name','Erreurs residuelles', ...
	   'Position',[0.38*L,0.1*H,0.3*L,0.7*H]);
    hold on;
    hx = xlabel('$x$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',15);
    histfit(residus_Dyx_MV,10);
    grid on;
    legend('Histogramme des residus','Loi normale estimee','Location','southoutside')
    title('Histogramme des erreurs residuelles')
    xlabel('Valeurs de l''erreur')
    ylabel('Effectif')

% Affichage des probabilites :
figure('Name','Probabilite de distribution normale', ...
	   'Position',[0.69*L,0.1*H,0.3*L,0.7*H]);
    hold on;
    hx = xlabel('$x$');
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$');
    set(hy,'Interpreter','Latex');
    set(gca,'FontSize',15);
    hnp = normplot(residus_Dyx_MV);
    set(hnp(1),'MarkerSize',7,'LineWidth',1);
    set(hnp(3),'LineStyle','-','LineWidth',2);
    grid on;
    legend([hnp(1) hnp(3)], ...
           'Proba pour les donnees', ...
           'Proba pour une loi normale', ...
           'Location','southeast')
    title('Comparaison des probabilites')
    xlabel('Valeurs des residus')
    ylabel('Probabilite')
 