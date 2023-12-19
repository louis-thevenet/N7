clear;
close all;
clc;

load donnees_exercice_1;

%--------------------------------------------------------------------------
% Calcul des coleurs moyennes
%--------------------------------------------------------------------------

% Couleurs moyennes des trois especes de fleurs :
X_pensees = single(zeros(nb_pensees,3));
Y = zeros(nb_pensees+nb_oeillets+nb_chrysanthemes,1);
indY = 1;
for i = 1:nb_pensees
	im = eval(['pe' num2str(i)]);
	X_pensees(i,:) = moyenne_normalisee_3v(im);
    Y(indY) = 1;
    indY = indY+1;
end
X_oeillets = single(zeros(nb_oeillets,3));
for i = 1:nb_oeillets
	im = eval(['oe' num2str(i)]);
	X_oeillets(i,:) = moyenne_normalisee_3v(im);
    Y(indY) = 2;
    indY = indY+1;
end
X_chrysanthemes = single(zeros(nb_chrysanthemes,3));
for i = 1:nb_chrysanthemes
	im = eval(['ch' num2str(i)]);
	X_chrysanthemes(i,:) = moyenne_normalisee_3v(im);
    Y(indY) = 3;
    indY = indY+1;
end

%--------------------------------------------------------------------------
% Affichage des donnees suivant les 3 categories de fleurs 
%--------------------------------------------------------------------------

figure('Name','Repartition des images suivant leurs couleurs moyennes',...
       'Position',[0.02*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
hold on;
plot3(X_pensees(:,1),X_pensees(:,2),X_pensees(:,3),'bx','MarkerSize',15,'LineWidth',3);
plot3(X_oeillets(:,1),X_oeillets(:,2),X_oeillets(:,3),'ro','MarkerSize',15,'LineWidth',3);
plot3(X_chrysanthemes(:,1),X_chrysanthemes(:,2),X_chrysanthemes(:,3),'c+','MarkerSize',15,'LineWidth',3);
axis xy;
grid on;
azimuth = -72;
elevation = 42;
view(azimuth,elevation);

title('Couleurs moyennes des images');
xlabel('$\bar{r}_p$','Interpreter','Latex');
ylabel('$\bar{v}_p$','Interpreter','Latex');
zlabel('$\bar{r}_c$','Interpreter','Latex');
legend('Pensees','Oeillets','Chrysantemes','Location','Best');
set(gca,'FontSize',15);

%--------------------------------------------------------------------------
% Partionnement en 3 clusters par les k-moyennes
%--------------------------------------------------------------------------

% Partitionnement des donnees :
X = [X_pensees ; X_oeillets ; X_chrysanthemes];
nb_clusters = length(unique(Y));
Y_pred = prediction_kmoyennes(X,nb_clusters);

% Evaluation numerique du partitionnement :
meilleur_pourcentage_partitionnement = calcul_bon_partitionnement(Y_pred,Y);

% Affichage de la partition :
couleur = [1 0 0 ; 0 1 1 ; 0 0 1];
leg = cell(1,3);
figure('Name','Repartition des images suivant les trois clusters',...
       'Position',[0.51*L,0.1*H,0.47*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
hold on;
for i = 1:nb_clusters
	indices_i = (Y_pred==i);
	leg{i} = plot3(X(indices_i,1),X(indices_i,2),X(indices_i,3),'*',...
                   'MarkerSize',15,'LineWidth',3,'Color',couleur(i,:));
end
axis xy;
grid on;
view(azimuth,elevation);

title(['Pourcentage de bon partitionnement = ' num2str(meilleur_pourcentage_partitionnement,'%.1f') '%']);
xlabel('$\bar{r}_p$','FontSize',30,'Interpreter','Latex');
ylabel('$\bar{v}_p$','FontSize',30,'Interpreter','Latex');
zlabel('$\bar{r}_c$','FontSize',30,'Interpreter','Latex');
legend([leg{1},leg{2},leg{3}],'Cluster 1','Cluster 2','Cluster 3','Location','Best');
set(gca,'FontSize',15);

