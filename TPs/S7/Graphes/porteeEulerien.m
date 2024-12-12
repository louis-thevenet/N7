%On peut generer une matrice random de grande taille ainsi
%S=rand(20,20)
%Distance=100*(S+S')/2
%Distance(logical(eye(20)))=Inf

function porteeEulerien(G)

[m,n]=size(G);

%Optional robust test: we must have square & symetric matrix
assert(n==m,'Input matrix must be square');
assert(isequal(G,G'),'Input matrix must be symetric');

G(logical(eye(n)))=Inf;

%reshaper la matrice sous forme de vecteur pour pouvoir trier ces valeurs
O=sort(reshape(G,1,m*n));
%toutes les distances>0
D=unique(O(O<Inf));%filtre les portees doublons et la portee infinie

%allocate vector to plot
eulerien=ones(size(D));

for i=1:size(D,2)
    A=G<=D(i);
    eulerien(i)=isEulerien(A);
end
%nv figure
figure;
plot(D,eulerien,'-x');
set(gca,'YTick',0:2); %0 1 & 2 Ytick
axis([0 D(end) 0 2]); %x/y min/max values
title('Pour quelle portee le graphe est il eulerien?');
