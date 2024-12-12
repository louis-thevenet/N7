function viz_spt(G,spt,pos,nodename)

%# of cities
n=size(nodename,2);

%PLOT SPT (first create new figure)
figure;

%DISPLAY CITIES NAME ON THE GRAPH
plot(pos(:,1),pos(:,2),'r.');hold on;  %display a red point for each city
for i=1:n
   text(pos(i,1)+5,pos(i,2), sprintf('%s (%d)\n',nodename{i},i));
end   

%MAKE A SPT GRAPH FROM THE SPT DATA
Gspt=zeros(n);
for i=1:n
    if spt(i)~=0
        Gspt(i,spt(i))=1;
        Gspt(spt(i),i)=1;
    end
end  
%DISPLAY SPT
gplot(Gspt,pos);
title('spt');