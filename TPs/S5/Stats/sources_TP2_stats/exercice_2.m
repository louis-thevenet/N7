exercice_0;
close all;

% Tirages aleatoires pour les 2 droites :
n_tirages = 5000;
[tirages_psi_1,tirages_G_1] = tirages_aleatoires_uniformes(n_tirages,taille); % FONCTION A CODER
[tirages_psi_2,tirages_G_2] = tirages_aleatoires_uniformes(n_tirages,taille); % FONCTION A CODER

% Estimation des 2 droites par le maximum de vraisemblance :
[a_Dyx_1MV,b_Dyx_1MV,a_Dyx_2MV,b_Dyx_2MV] = ...
estim_param_Dyx_MV_2droites(x_donnees_bruitees,y_donnees_bruitees,sigma, ...
                            tirages_G_1,tirages_psi_1,tirages_G_2,tirages_psi_2); % FONCTION A CODER

% Calcul de l'ecart angulaire cumule des 2 droites :
theta_Dyx_1MV = atan(-1/a_Dyx_1MV);
theta_Dyx_2MV = atan(-1/a_Dyx_2MV);
EA_Dyx_1MV_1VT = 180/pi*min(abs(theta_Dyx_1MV+[-pi,0,pi]-theta_1));
EA_Dyx_1MV_2VT = 180/pi*min(abs((theta_Dyx_1MV+[-pi,0,pi]-theta_2)));
EA_Dyx_2MV_1VT = 180/pi*min(abs((theta_Dyx_2MV+[-pi,0,pi]-theta_1)));
EA_Dyx_2MV_2VT = 180/pi*min(abs((theta_Dyx_2MV+[-pi,0,pi]-theta_2)));
EA_cumule_MV = min(EA_Dyx_1MV_1VT+EA_Dyx_2MV_2VT, EA_Dyx_1MV_2VT+EA_Dyx_2MV_1VT);
                                                
% Creation de la droite de regression 1 estimee par le maximum de vraisemblance :
x_Dyx_1MV = [-taille;x_donnees_bruitees;taille];
y_Dyx_1MV = a_Dyx_1MV*x_Dyx_1MV+b_Dyx_1MV;

% Creation de la droite de regression 2 estimee par le maximum de vraisemblance :
x_Dyx_2MV = [-taille;x_donnees_bruitees;taille];
y_Dyx_2MV = a_Dyx_2MV*x_Dyx_2MV+b_Dyx_2MV;   

% Affichage des droites : 
figure('Name','Estimations MV','Position',[0.02*L,0.1*H,0.31*L,0.7*H]);
    hold on;
    plot(x_droite,y_droite_1,'Color',[1,0,0],'LineWidth',3);
    plot(x_droite,y_droite_2,'Color',[0.6 0 0],'LineWidth',3,'HandleVisibility','off');
    plot(x_donnees_bruitees,y_donnees_bruitees,'k*','MarkerSize',5,'LineWidth',2);
    plot(x_Dyx_1MV,y_Dyx_1MV,'Color',[0 0 1],'LineWidth',3);
    plot(x_Dyx_2MV,y_Dyx_2MV,'Color',[0 0 0.6],'LineWidth',3,'HandleVisibility','off');
    axis(bornes);
    legend(' Droites_{VT} ', ...
           ' Donnees', ...
           ' Droites_{MV}',...
           'Location','northwest');
    axis equal;
    xlim([-taille taille]);
    ylim([-taille taille]);
    set(gca,'FontSize',15);
    hx = xlabel('$x$','FontSize',30);
    set(hx,'Interpreter','Latex');
    hy = ylabel('$y$','FontSize',30);
    set(hy,'Interpreter','Latex');
    grid on;
    title(['Ecarts angulaires MV = ' num2str(EA_cumule_MV,'%.2f') '°'])
    