clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Chemin d'acces aux images :
chemin = './Donnees/';
extension = '.png';

% Noms des images de la planete :
liste_noms = {'rouge','vert','bleu','altitude','distance','temperature','vent'};

% Affichage des images et stockage dans I :
figure('Name','Images de la planete Terre',...
       'Position',[0.02*L,0.1*H,0.96*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
I = [];
for i = 1:length(liste_noms)
	subplot(2,4,i);
	nom = liste_noms{i};
	img = imread([chemin nom extension]);
	img = rgb2gray(img);
	I = cat(3,I,img);
	imagesc(img);
	axis image off;
	colormap gray;
	title(nom);
	set(gca,'FontSize',25);
end

% Lecture du masque :
masque = imread([chemin 'masque' extension]);
masque = rgb2gray(masque);
subplot(2,4,length(liste_noms)+1);
imagesc(masque);
axis image off;
colormap gray;
title('masque');
set(gca,'FontSize',25);

clear chemin extension i img liste_noms nom taille_ecran;
save donnees_exercice_2;
