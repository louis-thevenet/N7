exercice_3;

figure('Name','Estimations EM','Position',[0.66*L,0.1*H,0.31*L,0.7*H]);

% Initialisation de l'algorithme EM :
seuil = 0.01;
dif_EA_cumule = 1;
a_Dyx_1MCP = a_Dyx_1MV;
b_Dyx_1MCP = b_Dyx_1MV;
a_Dyx_2MCP = a_Dyx_2MV;
b_Dyx_2MCP = b_Dyx_2MV;
EA_cumule = EA_cumule_MV;
n_iter = 0;
tic

while (abs(dif_EA_cumule) > seuil) && (toc < 5)

    n_iter = n_iter + 1;

    % Avec les 3 etapes ci-dessus dans une meme fonction
    [probas_classe_1,proportion_1,a_Dyx_1MCP,b_Dyx_1MCP,...
     probas_classe_2,proportion_2,a_Dyx_2MCP,b_Dyx_2MCP] = ...
    iteration_estim_param_Dyx_EM(x_donnees_bruitees,y_donnees_bruitees,sigma,...
                                 proportion_1,a_Dyx_1MCP,b_Dyx_1MCP,...
                                 proportion_2,a_Dyx_2MCP,b_Dyx_2MCP);

    % Classification des donnees (simplement pour les couleurs des points lors de l'affichage ici)
	[x_classe_1,y_classe_1,x_classe_2,y_classe_2] = ...
    classification_points(x_donnees_bruitees,y_donnees_bruitees,probas_classe_1,probas_classe_2);

    % Calcul de l'ecart angulaire cumule des 2 droites :
    theta_Dyx_1MCP = atan(-1/a_Dyx_1MCP);
    theta_Dyx_2MCP = atan(-1/a_Dyx_2MCP);
    EA_Dyx_1MCP_1VT = 180/pi*min(abs((theta_Dyx_1MCP+[-pi,0,pi]-theta_1)));
    EA_Dyx_1MCP_2VT = 180/pi*min(abs((theta_Dyx_1MCP+[-pi,0,pi]-theta_2)));
    EA_Dyx_2MCP_1VT = 180/pi*min(abs((theta_Dyx_2MCP+[-pi,0,pi]-theta_1)));
    EA_Dyx_2MCP_2VT = 180/pi*min(abs((theta_Dyx_2MCP+[-pi,0,pi]-theta_2)));
    nouveau_EA_cumule = min(EA_Dyx_1MCP_1VT+EA_Dyx_2MCP_2VT, EA_Dyx_1MCP_2VT+EA_Dyx_2MCP_1VT);
    dif_EA_cumule = nouveau_EA_cumule - EA_cumule;
    EA_cumule = nouveau_EA_cumule;

    % Affichage de la droite de regression 1 estimee par les moindres carres ponderes :
    x_Dyx_1MCP = [-taille;x_donnees_bruitees;taille];
    y_Dyx_1MCP = a_Dyx_1MCP*x_Dyx_1MCP+b_Dyx_1MCP;
    
    % Affichage de la droite de regression 2 estimee par les moindres carres ponderes :
    x_Dyx_2MCP = [-taille;x_donnees_bruitees;taille];
    y_Dyx_2MCP = a_Dyx_2MCP*x_Dyx_2MCP+b_Dyx_2MCP;
  
    % Affichage des droites :
    figure(3)
	hold off;
    hd = plot(x_droite,y_droite_1,'Color',[1,0,0],'LineWidth',3);
    hold on;
    plot(x_droite,y_droite_2,'Color',[0.6 0 0],'LineWidth',3);
	hc = plot(x_classe_1,y_classe_1,'Color',[1 0.8 0],'LineStyle','none','Marker','*','MarkerSize',5,'LineWidth',2);
    plot(x_classe_2,y_classe_2,'Color',[1 0.5 0],'LineStyle','none','Marker','*','MarkerSize',5,'LineWidth',2);
    hmcp = plot(x_Dyx_1MCP,y_Dyx_1MCP,'Color',[1 0.8 0],'LineWidth',3);
    plot(x_Dyx_2MCP,y_Dyx_2MCP,'Color',[1 0.5 0],'LineWidth',3);
    axis(bornes);
    legend([hd, hc, hmcp], ...
           ' Droites_{VT} ', ...
           ' Classes_{EM}', ...
           ' Droites_{EM}',...
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
    title({['Iteration ' num2str(n_iter) ' :'] ['Ecarts angulaires EM = ' num2str(EA_cumule,'%.2f') '°']})
    drawnow;

    pause(0.1);

end

