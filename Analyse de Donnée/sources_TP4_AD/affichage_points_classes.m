% fonction d'affichage des points avec la classe associee

function [f_ok,m_ok] = affichage_points_classes(X,Y,Y_pred)

    nb_donnees = size(Y,1);

    % Affichage des points :
    for i = 1:nb_donnees
        if Y(i) == 1 % Donnee reelle fibrome
            if Y_pred(i) == 1 % Prediction fibrome > bonne classification
                f_ok = plot(X(i,1),X(i,2),'bx','MarkerSize',10,'LineWidth',3);
            else % Prediction melanome > mauvaise classification
                plot(X(i,1),X(i,2),'kx','MarkerSize',10,'LineWidth',3);
            end
        else % Donnee reelle melanome
            if Y_pred(i) == 1 % Prediction fibrome > mauvaise classification
                plot(X(i,1),X(i,2),'ko','MarkerSize',10,'LineWidth',3);
            else % Prediction melanome > bonne classification
                m_ok = plot(X(i,1),X(i,2),'ro','MarkerSize',10,'LineWidth',3);
            end
        end
    end
end
