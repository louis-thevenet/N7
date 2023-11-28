clear;
close all;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Matrice des caracteristiques des donnees d'apprentissage :
load donnees_carac;
nb_donnees_app = size(Y_app,1);
nb_carac = size(X_app,2);
noms_carac = {'Compacite','Contraste','Texture'};
nb_classes = length(unique(Y_app));
noms_classes = {'Fibromes','Melanomes'};

% Affichage des deux nuages de points 3D :
figure('Name','Representation des images par des points 3D et 2D',...
       'Position',[0.05*L,0.1*H,0.9*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
subplot(1,2,1)
hold on;
for j = 1:nb_donnees_app
    switch Y_app(j)
        case 1 % Fibrome
            hf = plot3(X_app(j,1),X_app(j,2),X_app(j,3),'bx','MarkerSize',10,'LineWidth',3);
        case 2 % Melanome
            hm = plot3(X_app(j,1),X_app(j,2),X_app(j,3),'ro','MarkerSize',10,'LineWidth',3);
    end
end
view(45,45)
xlabel(noms_carac(1));
ylabel(noms_carac(2));
zlabel(noms_carac(3));
marge = 0.005;
axis([min(min(X_app(:,1)))-marge max(max(X_app(:,1)))+marge ...
      min(min(X_app(:,2)))-marge max(max(X_app(:,2)))+marge ...
      min(min(X_app(:,3)))-marge max(max(X_app(:,3)))+marge]);
grid on
title('Representation 3D')
legend([hf,hm],noms_classes,'Location','NorthWest');
set(gca,'FontSize',20);

% Affichage de la grille du maximum de vraisemblance :
for k = 1:nb_carac
    subplot(3,2,2*k)
    num_carac_x = 1+mod(k-1,3);
    num_carac_y = 1+mod(k,3);
    hold on;
    affichage_points_classes([X_app(:,num_carac_x),X_app(:,num_carac_y)],Y_app,Y_app);
    xlabel(noms_carac(num_carac_x))
    ylabel(noms_carac(num_carac_y))
    axis([min(min(X_app(:,num_carac_x)))-marge max(max(X_app(:,num_carac_x)))+marge ...
          min(min(X_app(:,num_carac_y)))-marge max(max(X_app(:,num_carac_y)))+marge]);
    grid on
    if k == 1
        title('Representations 2D')
    end
    legend([hf,hm],noms_classes,'Location','Best');
    set(gca,'FontSize',15);
end


