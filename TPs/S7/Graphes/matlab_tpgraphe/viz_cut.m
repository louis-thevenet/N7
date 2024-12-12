function viz_cut(G,cut,pos,nodename,srcs,dsts)

%# of cities
n=size(nodename,2);

%PLOT MST (first create new figure)
figure;

%DISPLAY CITIES NAME ON THE GRAPH
plot(pos(:,1),pos(:,2),'r.');hold on;  %display a red point for each city
for i=1:n
   text(pos(i,1)+5,pos(i,2), sprintf('%s (%d)\n',nodename{i},i));
end   

%MAKE A CUT GRAPH FROM THE CUT DATA
Gcut=zeros(n);
for i=1:n
    for j=1:n
        if ((i~=j) && (cut(i)==1) && (cut(j)==-1) && (G(i,j)>0))
            Gcut(i,j)=1;
            Gcut(j,i)=1;
        end
    end
end

%DISPLAY CUT
%first display src & dst 
plot(pos(srcs,1),pos(srcs,2),'ro','LineWidth',2);hold on;
plot(pos(dsts,1),pos(dsts,2),'r+','LineWidth',2);hold on;

%then graph
gplot(G(1:n,1:n),pos,'-b');hold on;
%tehn cut
[X,Y]=gplot(Gcut,pos);
%to change linewidth we have to use plot (gplot does not plot if it returns args)
plot (X, Y, ':r', 'LineWidth', 4) ;
title('cut');
