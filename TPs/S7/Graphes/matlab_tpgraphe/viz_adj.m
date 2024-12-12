function viz_adj(G,A,pos,nodename)

%# of cities
n=size(nodename,2);

%PLOT GRAPH(first create new figure)
figure;

%DISPLAY CITIES NAME ON THE GRAPH
plot(pos(:,1),pos(:,2),'r.');hold on;  %display a red point for each city
for i=1:n
   %text(pos(i,1)+5,pos(i,2), [nodename(i) '(' int2str(i) ')']); %with the name of the city
   text(pos(i,1)+5,pos(i,2), sprintf('%s (%d)\n',nodename{i},i));
end   

%DISPLAY SPT
gplot(sparse(A),pos);
title('adj');