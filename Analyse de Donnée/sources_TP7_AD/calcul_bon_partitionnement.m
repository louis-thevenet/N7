% fonction calcul_bon_partitionnement (pour l'exercice 1)

function meilleur_pourcentage_partitionnement = calcul_bon_partitionnement(Y_pred,Y)

Permutations = perms(1:3);
max = .0;
for i=1:6
    Y_temp = Y_pred;

    Y_temp(Y_pred==1) = Permutations(i,1);
    Y_temp(Y_pred==2) = Permutations(i,2);
    Y_temp(Y_pred==3) = Permutations(i,3);

    n = nnz(Y==Y_temp);
    if max < n 
        max =n;
    end

end
meilleur_pourcentage_partitionnement = (max*100) / length(Y);
end