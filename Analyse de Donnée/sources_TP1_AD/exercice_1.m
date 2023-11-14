clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

figure('Name','Visualisation des canaux RVB (en 3D et canal par canal)',...
       'Position',[0.1*L,0.1*H,0.8*L,0.7*H], ...
       'Color',[0.7 0.75 0.85]);

% Lecture d'une image RVB :
I = imread('autumn.tif');
% I = imread('image.png');

% Decoupage de l'image en trois canaux et conversion en doubles :
R = double(I(:,:,1));
V = double(I(:,:,2));
B = double(I(:,:,3));

% Calcul des correlations et contrastes :
X = [R(:) V(:) B(:)];	
[correlation,contraste] = correlation_contraste(X); % FONCTION A CODER

% Affichage du nuage de pixels dans le repere RVB :
subplot(1,3,1);
plot3(R,V,B,'.','MarkerSize',3,'Color',"#4DBEEE")
axis equal;
set(gca,'FontSize',10);
xlabel('Rouge','FontWeight','bold','FontSize',15,'Color','red')
ylabel('Vert','FontWeight','bold','FontSize',15,'Color','green')
zlabel('Bleu','FontWeight','bold','FontSize',15,'Color','blue')
view([45 20])
rotate3d;
grid on;
title({'Representation 3D des pixels' ...
       'dans l''espace RVB'},'FontSize',20)
   
% Affichage de l'image RVB :
subplot(3,3,2);
imagesc(I);
axis image off;
title('Image RVB','FontSize',20);

% Affichage des correlations :
subplot(7,3,11);
axis off
title(['r_{\color{red}R\color{green}V\color{black}} = ' num2str(correlation(1),'%.2f')],'FontSize',20);

% Affichage des correlations :
subplot(7,3,14);
axis off
title(['r_{\color{red}R\color{blue}B\color{black}} = ' num2str(correlation(2),'%.2f')],'FontSize',20);

% Affichage des correlations :
subplot(7,3,17);
axis off
title(['r_{\color{green}V\color{blue}B\color{black}} = ' num2str(correlation(3),'%.2f')],'FontSize',20);

% Affichage du canal R :
colormap gray;
subplot(3,3,3);
imagesc(R);
clim([0 255]);
colorbar;
axis image off;
title(['Canal \color{red}Rouge\color{black} > contraste = ' num2str(100*contraste(1),'%.1f') '%'],'FontSize',20);

% Affichage du canal V :
subplot(3,3,6);
imagesc(V);
clim([0 255]);
colorbar;
axis image off;
title(['Canal \color{green}Vert\color{black} > contraste = ' num2str(100*contraste(2),'%.1f') '%'],'FontSize',20);

% Affichage du canal B :
subplot(3,3,9);
imagesc(B);
clim([0 255]);
colorbar;
axis image off;
title(['Canal \color{blue}Bleu\color{black} > contraste = ' num2str(100*contraste(3),'%.1f') '%'],'FontSize',20);
