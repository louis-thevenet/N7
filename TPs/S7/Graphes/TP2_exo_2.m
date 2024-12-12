%%%%% SET ENV %%%%%

addpath('matlab_bgl');      %load graph libraries
addpath('matlab_tpgraphe'); %load tp ressources
load TPgraphe.mat;          %load data

%%%%%%%%%%%%%%%%%%%%%% INIT %%%%%%%%%%%%%%%%%%%%%%%%%%%%
%First generate random matrix & make it sparse to use graph libraries

%Q2.1 tracer le nombre de composantes connexes dans D
[u v]=components(sparse(D));
figure;
hist(v,size(D,1));

%Q2.2 etudier la repartition du # de composantes connexes dans un grand graphe random 
%en fct de la densite des liens
n=100;
density=[5 8 10 15 20 30]; %density in percent
S=sparse(randi(100,n));%generate n*n matrix of values uni distributed in in 1:100
S=(S+S')/2;%make a symetric matrix

figure;
for i=1:size(density,2)  
    A=S<density(i);%adjacency  matrix 
    [u v]=components(sparse(A));
    subplot(2,3,i);  %plot the figure in a new vignette of a 6 vignette plot
    hist(v,size(A,1));
    title(sprintf('Densite=%d%%',density(i)));
end
