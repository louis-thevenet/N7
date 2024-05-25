function out = binary2vector(data,nBits)

powOf2 = 2.^[0:nBits-1];

%# do a tiny bit of error-checking
if data > sum(powOf2)
   error('not enough bits to represent the data')
end

out = false(length(data),nBits);

for i =1:length(data)

ct = nBits;
    while data(i)>0
    if data(i) >= powOf2(ct)
    data(i) = data(i)-powOf2(ct);
    out(i,ct) = true;
    end
    ct = ct - 1;
    end
end
