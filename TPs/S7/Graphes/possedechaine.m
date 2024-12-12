function [chaineExiste] = possedechaine(G,chaine)
%POSSEDECHAINE Summary of this function goes here
%   Detailed explanation goes here

for i = 1:(length(chaine)-1)
    u = chaine(i);
    v = chaine(i+1);

    if G(u, v)<=0
        chaineExiste=false;
        return;
    end


end
chaineExiste =true;
end

