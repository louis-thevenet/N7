% Fonction ecriture_RVB

function image_RVB = ecriture_RVB(image_originale)

    [taille_y, taille_x]=size(image_originale);
    taille_y = taille_y/2;
    taille_x = taille_x/2;

    R = image_originale(1:2:(2*taille_y), 2:2:(2*taille_x));
    B = image_originale(2:2:(2*taille_y), 1:2:(2*taille_x));
    V = (image_originale(1:2:(2*taille_y), 1:2:(2*taille_x)) + image_originale(2:2:(2*taille_y), 2:2:(2*taille_x)))/2;

    image_RVB = cat(3,R,V,B);

    for j=1:taille_y
        for i=1:taille_x/2
            tmp = image_RVB(j,i, :);
            image_RVB(j,i, :)=image_RVB(j, taille_x-i, :);
            image_RVB(j, taille_x-i, :)=tmp;
        end
    end

