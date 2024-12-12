function [isEulerien] = isEulerien(A)
%ISEULERIEN Summary of this function goes here
%   Detailed explanation goes here
    degres = sum(A);
    isEulerien = sum(mod(degres,2)) == 2 || sum(mod(degres,2)) == 0;
end

