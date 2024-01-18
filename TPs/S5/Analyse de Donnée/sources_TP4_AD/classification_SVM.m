% fonction classification_SVM (pour l'exercice 1)

function Y_pred = classification_SVM(X,w,c)

Y_pred = sign(w'*X' - c);

end
