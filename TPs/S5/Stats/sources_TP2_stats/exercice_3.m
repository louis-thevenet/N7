exercice_2;

% Proportions de depart :
proportion_1 = 0.5;
proportion_2 = 1 - proportion_1;

% Calcul des probablites d'appartenance aux 2 classes : 
[probas_classe_1,probas_classe_2] = ...
probabilites_classe(x_donnees_bruitees,y_donnees_bruitees,sigma,...
                    a_Dyx_1MV,b_Dyx_1MV,proportion_1,...
                    a_Dyx_2MV,b_Dyx_2MV,proportion_2);

% Classification des donnees :
[x_classe_1,y_classe_1,x_classe_2,y_classe_2] = ...
classification_points(x_donnees_bruitees,y_donnees_bruitees,...
                      probas_classe_1,probas_classe_2);

% Estimation des 2 droites par les moindres carres pour chaque classe :
[a_Dyx_1MC,b_Dyx_1MC] = estim_param_Dyx_MC(x_classe_1,y_classe_1);
[a_Dyx_2MC,b_Dyx_2MC] = estim_param_Dyx_MC(x_classe_2,y_classe_2);

% Calcul de l'ecart angulaire cumule des 2 droites :
theta_Dyx_1MC = atan(-1/a_Dyx_1MC);
theta_Dyx_2MC = atan(-1/a_Dyx_2MC);
EA_Dyx_1MC_1VT = 180/pi*min(abs((theta_Dyx_1MC+[-pi,0,pi]-theta_1)));
EA_Dyx_1MC_2VT = 180/pi*min(abs((theta_Dyx_1MC+[-pi,0,pi]-theta_2)));
EA_Dyx_2MC_1VT = 180/pi*min(abs((theta_Dyx_2MC+[-pi,0,pi]-theta_1)));
EA_Dyx_2MC_2VT = 180/pi*min(abs((theta_Dyx_2MC+[-pi,0,pi]-theta_2)));
EA_cumule_MC = min(EA_Dyx_1MC_1VT+EA_Dyx_2MC_2VT, EA_Dyx_1MC_2VT+EA_Dyx_2MC_1VT);

% Creation de la droite de regression 1 estimee par les moindres carres :
x_Dyx_1MC = [-taille;x_donnees_bruitees;taille];
y_Dyx_1MC = a_Dyx_1MC*x_Dyx_1MC+b_Dyx_1MC;

% Creation de la droite de regression 2 estimee par les moindres carres :
x_Dyx_2MC = [-taille;x_donnees_bruitees;taille];
y_Dyx_2MC = a_Dyx_2MC*x_Dyx_2MC+b_Dyx_2MC;

% Affichage des droites :
figure('Name','Estimations MC','Position',[0.34*L,0.1*H,0.31*L,0.7*H]);
    hold on;
    hd = plot(x_droite,y_droite_1,'Color',[1,0,0],'LineWidth',3);
    plot(x_droite,y_droite_2,'Color',[0.6 0 0],'LineWidth',3);
    hc = plot(x_classe_1,y_classe_1,'Color',[0 1 0],'LineStyle','none','Marker','*','MarkerSize',5,'LineWidth',2);
    plot(x_classe_2,y_classe_2,'Color',[0 0.6 0],'LineStyle','none','Marker','*','MarkerSize',5,'LineWidth',2);
    hmc = plot(x_Dyx_1MC,y_Dyx_1MC,'Color',[0 1 0],'LineWidth',3);
    plot(x_Dyx_2MC,y_Dyx_2MC,'Color',[0 0.6 0],'LineWidth',3);
    axis(bornes);
    legend([hd, hc, hmc], ...
           ' Droites_{VT} ', ...
           ' Classes_{MV}', ...
           ' Droites_{MC}',...
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
    title(['Ecarts angulaires MC = ' num2str(EA_cumule_MC,'%.2f') '°'])
