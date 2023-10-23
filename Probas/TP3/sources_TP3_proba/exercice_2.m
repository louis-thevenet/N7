clear;
close all;
clc;

load exercice_1;

% Parametres :
p = alpha/pi;
epsilon = 1e-20;

% Affichage de l'image :
figure('Name','Detection des alignements','Position',[0.1*L,0.1*H,0.8*L,0.65*H]);
subplot(1,2,1);
    imagesc(I);
    axis image off;
    colormap gray;
    title('L''image','FontSize',30);
    drawnow;

% Affichage d'un fond gris pour l'esquisse :
subplot(1,2,2);
    imagesc(120*ones(size(I)),[0,255]);
    axis image off
    colormap gray;
    title('Candidats conserves','FontSize',30);
    hold on;

% Boucle sur les ensembles E :
nb_elimines = 0;

for k = 1:length(liste_E)

	% Calcul de la matrice d'inertie de l'ensemble candidat numero k :
	E = fliplr(liste_E{k}); % Car x = j et y = i		
	indices_E = sub2ind(size(I),E);
	G_norme_E = G_norme(indices_E);
	[M_inertie,C] = matrice_inertie(E,G_norme_E);

	% Calcul des valeurs/vecteurs propres de M :
	[V,D] = eig(M_inertie);

	% Tri des valeurs propres de M par ordre decroissant :
	[~,indices] = sort(diag(D),'descend');

	% Matrice de passage du repere xy vers les axes propres du nuage de points :
	P = V(:,indices);

	% Coordonnees des points du nuage apres rotation dans le repere des axes principaux :
    % (il faut encore une fois intervertir les colonnes de E)
	E_nouveau_repere = (E-C)*P;

	% Calcul de probabilite (loi binomiale) :
	[x_min,x_max,probabilite] = calcul_proba(E_nouveau_repere,p);

	% Test de saillance visuelle :
	if (probabilite < epsilon)		% Si l'evenement est suffisamment rare
		% Affichage du segment :
		extremites = P*[x_min x_max ; 0 0] + [C' , C'];
		line(extremites(1,:),extremites(2,:),'Color','w','LineWidth',2);
		drawnow;
    else
        % Affichage du segment :
		extremites = P*[x_min x_max ; 0 0] + [C' , C'];
		line(extremites(1,:),extremites(2,:),'Color','r','LineWidth',2);
		drawnow;
		nb_elimines = nb_elimines+1;
	end
end

title([num2str(nb_elimines) ' candidats elimines sur ' num2str(length(liste_E))]);
