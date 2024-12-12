function viz_mst(G,Gmst,pos,nodename)

%# of cities
n=size(nodename,2);

%PLOT MST (first create new figure)
figure;

%DISPLAY CITIES NAME ON THE GRAPH
plot(pos(:,1),pos(:,2),'r.');hold on; %display a red point for each city
for i=1:n
   text(pos(i,1)+5,pos(i,2), sprintf('%s (%d)\n',nodename{i},i));
end   

%DISPLAY MST
gplot(Gmst,pos);
title('mst');