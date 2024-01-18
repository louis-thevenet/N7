#include "complexe.h"
#include <math.h> // Pour certaines fonctions trigo notamment

// Implantations de reelle et imaginaire

double reelle(complexe_t c)
{
    return c.partie_reelle;
}

double imaginaire(complexe_t c)
{
    return c.partie_imaginaire;
}

// Implantations de set_reelle et set_imaginaire

void set_reelle(complexe_t *c, double v)
{
    c->partie_reelle = v;
}

void set_imaginaire(complexe_t *c, double v)
{
    c->partie_imaginaire = v;
}

void init(complexe_t *c, double a, double b)
{
    set_reelle(c, a);
    set_imaginaire(c, b);
}

// Implantation de copie
void copie(complexe_t *resultat, complexe_t autre)
{
    resultat->partie_reelle = autre.partie_reelle;
    resultat->partie_imaginaire = autre.partie_imaginaire;
}

// Implantations des fonctions algébriques sur les complexes

void conjugue(complexe_t *resultat, complexe_t op)
{
    init(resultat, op.partie_reelle, -op.partie_imaginaire);
}

void ajouter(complexe_t *resultat, complexe_t gauche, complexe_t droite)
{
    init(resultat, gauche.partie_reelle + droite.partie_reelle, gauche.partie_imaginaire + droite.partie_imaginaire);
}

void soustraire(complexe_t *resultat, complexe_t gauche, complexe_t droite)
{
    init(resultat, gauche.partie_reelle - droite.partie_reelle, gauche.partie_imaginaire - droite.partie_imaginaire);
}

void multiplier(complexe_t *resultat, complexe_t gauche, complexe_t droite)
{
    init(
        resultat,
        gauche.partie_reelle * droite.partie_reelle - gauche.partie_imaginaire * droite.partie_imaginaire,
        gauche.partie_reelle * droite.partie_imaginaire + gauche.partie_imaginaire * droite.partie_reelle);
}

void echelle(complexe_t *resultat, complexe_t op, double facteur) { init(resultat, op.partie_reelle * facteur, op.partie_imaginaire * facteur); }

void puissance(complexe_t *resultat, complexe_t op, int exposant)
{
    if (exposant == 0)
    {
        init(resultat, 1, 0);
        return;
    }

    *resultat = op;
    for (int k = 0; k < exposant - 1; k++)
    {
        multiplier(resultat, *resultat, op);
    }
}

/** PROCÉDURE puissance À IMPLANTER **/

// Implantations du module et de l'argument
double module_carre(complexe_t c)
{
    return c.partie_reelle * c.partie_reelle + c.partie_imaginaire * c.partie_imaginaire;
}

double module(complexe_t c)
{
    return sqrt(module_carre(c));
}

double argument(complexe_t c) { return 2 * atan(c.partie_imaginaire / (c.partie_reelle + module(c))); }