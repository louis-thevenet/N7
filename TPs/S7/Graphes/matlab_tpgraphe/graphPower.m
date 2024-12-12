%boolean A + A^2 + A^3 + A^4 +...+ A^k
function P=graphPower(A,k)
[m,n]=size(A);
Anew=eye(n);
Aprev=zeros(n);
P=Aprev;
while (k>0) && nnz(Anew-Aprev)>0 %if Anew==Aprev stops (see cours)
    Aprev=Anew;
    Anew=bmul(Aprev,A);
    k=k-1;
    P=badd(P,Anew);%add A^i to P
end