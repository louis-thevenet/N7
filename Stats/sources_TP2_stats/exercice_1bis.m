exercice_1;

% Estimation de la droite de regression par les moindres carres :
[a_Dyx_MC,b_Dyx_MC] = estim_param_Dyx_MC(x_donnees_bruitees,y_donnees_bruitees); % FONCTION A CODER

% Creation de la droite estimee par les moindres carres :
x_Dyx_MC = [-taille;x_donnees_bruitees;taille];
y_Dyx_MC = a_Dyx_MC*x_Dyx_MC+b_Dyx_MC;

% Affichage des droites :
hold on;
plot(x_Dyx_MC,y_Dyx_MC,'Color',[0 0.8 0],'LineWidth',3);
axis(bornes);
legend(' Droites_{VT} ', ...
       ' Donnees', ...
       ' Droite_{MV}', ...
       ' Droite_{MC}', ...
       'Location','Best');
axis equal;
xlim([-taille taille]);
ylim([-taille taille]);
set(gca,'FontSize',15);
hx = xlabel('$x$','FontSize',30);
set(hx,'Interpreter','Latex');
hy = ylabel('$y$','FontSize',30);
set(hy,'Interpreter','Latex');
grid on;
