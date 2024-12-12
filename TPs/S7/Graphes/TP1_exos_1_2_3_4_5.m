%%%%% SET ENV %%%%%

addpath('matlab_bgl');      %load graph libraries
addpath('matlab_tpgraphe'); %load tp ressources

load TPgraphe.mat;          %load data

%%%%%% DISPLAY INPUT DATA ON TERMINAL %%%%%

cities; %names of cities
D ;     %distance matrix bw cities
pos ;   %x-y pos of the cities

%%%%%%EXO 1 (modeliser et afficher le graphe) %%%%%

d=500;

A=D<=d; %adj matrix

viz_adj(D,A,pos,cities);
%viz_adj(D,graphPower(A, 2),pos,cities);
%viz_adj(D,graphPower(A, 3),pos,cities);
%viz_adj(D,graphPower(A, 10),pos,cities);
%viz_adj(D,graphPower(A, 12),pos,cities);
% Plus n est grand, plus la longueur du chemin est grande

%%%%%% EXO 2 %%%%%

%Q1 - existence d'un chemin de longueur 3
nnz((graphPower(A, 3)>0) - (graphPower(A, 2)>0)) > 0

%Q2 - nb de chemins de 3 sauts
nnz((graphPower(A, 3)>0) - (graphPower(A, 2)>0))

%Q3 - nb de chemins <=3
nnz((graphPower(A, 3)>0))

%%%%%%%% EXO 3 %%%%%
% Les paires de sommets doivent correspondre à une arrete du graphe
print("Les chaines sont-elles dans le graphe ?")
c=[18 13 9]; %la chaine 18 13 9 est t dans le graphe?
possedechaine(A,c)
c=[18 6 3]; %la chaine 18 6 3 est t dans le graphe?
possedechaine(A,c)
c=[26 5 17]; %la chaine 26 5 17 est t dans le graphe?
possedechaine(A,c)

%%%%%%%% EXO 4%%%%%
isEulerien(A)

%%%%%%%% EXO 5%%%%%
porteeEulerien(D)
