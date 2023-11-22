clear;
close all;
clc;

taille_ecran = get(0,'ScreenSize');
L = taille_ecran(3);
H = taille_ecran(4);

% Chargement des donnees :
load donnees;

% Affichage des silhouettes de la flamme :
figure('Name','Silhouettes d''une flamme de bougie',...
       'Position',[0.2*L,0.1*H,0.6*L,0.7*H],...
       'Color',[0.7 0.75 0.85]);
   
[p,n] = size(bord_inf);
x = transpose(0:1/(p-1):1);
for j = 1:n
	plot(x,bord_inf(:,j),'k*-','LineWidth',2);
	hold on;
	plot(x,bord_sup(:,j),'k*-','LineWidth',2);
	axis([0,1.01,60,150]);
	axis ij;
    grid on;
    hold off;
    
    title('Representation des points des silouhettes des flammes');
    legend('Donnees');
	set(gca,'FontSize',20);
	xlabel('$x$','FontSize',30,'Interpreter','Latex');
	ylabel('$y$','FontSize',30,'Interpreter','Latex','Rotation',0);
	pause(0.5);
	
end
