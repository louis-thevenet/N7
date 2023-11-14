clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

figure('Name','Visualisation des canaux RVB',...
       'Position',[0.1*L,0.1*H,0.8*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);

% Lecture d'une image RVB :
I = imread('autumn.tif');

% Decoupage de l'image en trois canaux et conversion en doubles :
R = double(I(:,:,1));
V = double(I(:,:,2));
B = double(I(:,:,3));
   
% Affichage de l'image RVB :
subplot(1,3,1);
imagesc(I);
axis image off;
title('Image RVB','FontSize',20);

% Affichage du filtrage R :
subplot(3,3,2);
imagesc(uint8(cat(3,R,V*0,B*0)));
axis image off;
title('Filtrage rouge','FontSize',20);

% Affichage du filtrage V :
subplot(3,3,5);
imagesc(uint8(cat(3,R*0,V,B*0)));
axis image off;
title('Filtrage vert','FontSize',20);

% Affichage du filtrage B :
subplot(3,3,8);
imagesc(uint8(cat(3,R*0,V*0,B)));
axis image off;
title('Filtrage bleu','FontSize',20);

% Affichage du canal R :
colormap gray;
subplot(3,3,3);
imagesc(R);
clim([0 255]);
colorbar;
axis image off;
title('Canal \color{red}Rouge\color{black} seul','FontSize',20);

% Affichage du canal V :
subplot(3,3,6);
imagesc(V);
clim([0 255]);
colorbar;
axis image off;
title('Canal \color{green}Vert\color{black} seul','FontSize',20);

% Affichage du canal B :
subplot(3,3,9);
imagesc(B);
clim([0 255]);
colorbar;
axis image off;
title('Canal \color{blue}Bleu\color{black} seul','FontSize',20);
