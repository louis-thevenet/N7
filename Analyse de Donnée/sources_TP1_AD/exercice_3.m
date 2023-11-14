clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

figure('Name','ACP d''une image RVB',...
       'Position',[0.1*L,0.1*H,0.8*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);

% Lecture d'une image RVB :
I = imread('image.png');

% Modification de la couleur des pixels blancs :
I = noircir_pixels_blancs(I); % FONCTION A CODER

% Decoupage de l'image modifiee en trois canaux et conversion en doubles :
R = double(I(:,:,1));
V = double(I(:,:,2));
B = double(I(:,:,3));

% Matrice des donnees :
X = [R(:) V(:) B(:)];		% Les trois canaux sont vectorises et concatenes

% Analyse en composantes principales de la matrice X des donnees :
[C,bornes_C] = ACP(X); % FONCTION A CODER
C1 = C(:,1);
C2 = C(:,2);
C3 = C(:,3);

% Calcul des correlations et contrastes :
[correlation,contraste] = correlation_contraste(C); % FONCTION A CODER

% Affichage du nuage de pixels dans le repere des composantes principales :
subplot(1,3,1);
plot3(C1,C2,C3,'.','MarkerSize',3,'Color',"#4DBEEE")
axis equal;
set(gca,'FontSize',10);
xlabel('C_1','FontWeight','bold','FontSize',15)
ylabel('C_2','FontWeight','bold','FontSize',15)
zlabel('C_3','FontWeight','bold','FontSize',15)
view([105 30])
rotate3d;
grid on;
title({'Representation 3D des pixels dans' ...
       'l''espace des composantes principales'},'FontSize',20)

% Affichage de l'image RVB :
subplot(3,3,2);
imagesc(uint8(I));
axis image off;
title('Image RVB','FontSize',20);

% Affichage des correlations :
subplot(7,3,11);
axis off
title(['r_{C_1C_2} = ' num2str(correlation(1),'%.2f')],'FontSize',20);

% Affichage des correlations :
subplot(7,3,14);
axis off
title(['r_{C_1C_3} = ' num2str(correlation(2),'%.2f')],'FontSize',20);

% Affichage des correlations :
subplot(7,3,17);
axis off
title(['r_{C_2C_3} = ' num2str(correlation(3),'%.2f')],'FontSize',20);
   
% Affichage de la premiere composante principale :
colormap gray;				% Pour afficher les images en niveaux de gris
subplot(3,3,3);
imagesc(reshape(C1,size(R)));
clim(bornes_C)
axis image off;
colorbar;
title(['Composante n°1 > contraste = ' num2str(100*contraste(1),'%.1f') '%'],'FontSize',20);

% Affichage de la deuxieme composante principale :
subplot(3,3,6);
imagesc(reshape(C2,size(V)));
clim(bornes_C)
axis image off;
colorbar;
title(['Composante n°2 > contraste = ' num2str(100*contraste(2),'%.1f') '%'],'FontSize',20);

% Affichage de la troisieme composante principale :
subplot(3,3,9);
imagesc(reshape(C3,size(B)));
clim(bornes_C)
axis image off;
colorbar;
title(['Composante n°3 > contraste = ' num2str(100*contraste(3),'%.1f') '%'],'FontSize',20);
