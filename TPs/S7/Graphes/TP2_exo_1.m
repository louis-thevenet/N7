%%%%% TP2_exo_1.m %%%%%

addpath('matlab_bgl');      %load graph libraries
addpath('matlab_tpgraphe'); %load tp ressources

%load TPgraphe.mat;          %load data
dataGermany();

%%%%%%%%%%%%%%%%%%%%%% INIT %%%%%%%%%%%%%%%%%%%%%%%%%%%%
G=sparse(D);

%%%%%%%%%%%%%%%%%%%%%% EXO SPT %%%%%%%%%%%%%%%%%%%%%%%%%%%%

%0)Choose arbitrary src node for spt
src=14;
%1)Compute SPT rooted in src node
[wp spt_]=shortest_paths(G,src); %wp=weight path, spt_=shortsetpathtree structure
%2)Vizualize
viz_spt(G,spt_,pos,cities);

%%%%%%%%%%%%%%%%%%%%%% EXO MST %%%%%%%%%%%%%%%%%%%%%%%%%%%%

%1)Compute MST by PRIM 
%changer les valeurs initiales pour obtenir deux arbres differents entre PRIM et KRUSKAL
GP=G;
GP(1,2)=1;
GP(2,1)=1;

GP(1,3)=1;
GP(3,1)=1;

GP(3,2)=1;
GP(2,3)=1;
load TPgraphe.mat; 
mst_=prim_mst(GP,struct('root',1));
%2)Vizualize
viz_mst(GP,mst_,pos,cities);


%1)Compute MST by KRUSKAL
mst_=kruskal_mst(GP);

%2)Vizualize10
viz_mst(GP,mst_,pos,cities);


%%%%%%%%%%%%%%%%%%%%%% EXO FLOW/CUT %%%%%%%%%%%%%%%%%%%%%%%%%%%%
    
%0)Choose arbitrary srcs, dsts and virtual capacities for these nodes

%srcs=[18, 24]; %for europe
%dsts=[7, 26];  %for europe

srcs=[1,2]; %for europe
dsts=[19,20];  %for europe

% virtual_capacity=100;%for europe
virtual_capacity=10000;%for germany

%1)create bandwdth graph from distance graph
n=size(D,1);
%add virtual src & dst (so create graph with two extra nodes)
bw=zeros(n+2,n+2);
%n+1th node is for virtual src;virtual src connected to srcs cities
bw(n+1,srcs)=virtual_capacity; 
bw(srcs,n+1)=virtual_capacity; 
%n+2th node is for virtual dst;virtual dst connected to dsts cities
bw(n+2,dsts)=virtual_capacity; 
bw(dsts,n+2)=virtual_capacity; 

%bandwidth is invertly proportinal to distance

bw(1:n,1:n)=10000./D;

%Inf is on the diagonal, so change it to 0
bw(bw==Inf)=0;
%links with too less bw are not interesting for operators
%bw(bw<=11)=0;%for europe
bw(bw<=120)=0;%for europe

%2)Compute Max flow bw virtual src & dst nodes
Gbw=sparse(bw);
[max_val cut_ R F]=max_flow(Gbw,n+1,n+2);

%3)Vizualize
viz_cut(Gbw,cut_,pos,cities,srcs,dsts)




