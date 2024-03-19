#include <stdio.h>
#include <stdlib.h>
#include "tests.h"
#include "tab.h"

int main() {
    BEGIN_SECTION("tab_t")
        BEGIN_TESTI("creer-detruire")
            struct tab_t* tab = creer();
            ASSERT_EQ(taille(tab), 0);
            ASSERT_EQ(espace(tab), 4);
            detruire(&tab);
        END_TEST

        BEGIN_TESTI("ajouter-1")
            struct tab_t* tab = creer();
            ajouter(tab, 1);
            ajouter(tab, 2);
            ajouter(tab, 3);
            ASSERT_EQ(taille(tab), 3);
            ASSERT_EQ(espace(tab), 4);
            ASSERT_EQ(element(tab, 0), 1);
            ASSERT_EQ(element(tab, 1), 2);
            ASSERT_EQ(element(tab, 2), 3);
            detruire(&tab);
        END_TEST

        BEGIN_TESTI("ajouter-realloc")
            struct tab_t* tab = creer();
            ajouter(tab, 1);
            ajouter(tab, 2);
            ajouter(tab, 3);
            ajouter(tab, 4);
            ajouter(tab, 5);
            ajouter(tab, 6);
            ASSERT_EQ(taille(tab), 6);
            ASSERT_EQ(espace(tab), 8);
            ASSERT_EQ(element(tab, 0), 1);
            ASSERT_EQ(element(tab, 1), 2);
            ASSERT_EQ(element(tab, 2), 3);
            ASSERT_EQ(element(tab, 3), 4);
            ASSERT_EQ(element(tab, 4), 5);
            ASSERT_EQ(element(tab, 5), 6);
            detruire(&tab);
        END_TEST

        BEGIN_TESTI("supprimer")
            struct tab_t* tab = creer();
            ajouter(tab, 1);
            ajouter(tab, 2);
            ajouter(tab, 3);
            ajouter(tab, 4);
            ajouter(tab, 5);
            ajouter(tab, 6);
            supprimer(tab, 2);
            ASSERT_EQ(taille(tab), 5);
            ASSERT_EQ(espace(tab), 8);
            ASSERT_EQ(element(tab, 0), 1);
            ASSERT_EQ(element(tab, 1), 3);
            ASSERT_EQ(element(tab, 2), 4);
            ASSERT_EQ(element(tab, 3), 5);
            ASSERT_EQ(element(tab, 4), 6);
            detruire(&tab);
        END_TEST

        BEGIN_TESTI("supprimer-multiples-occurrences")
            struct tab_t* tab = creer();
            ajouter(tab, 1);
            ajouter(tab, 2);
            ajouter(tab, 3);
            ajouter(tab, 2);
            ajouter(tab, 2);
            supprimer(tab, 2);
            ASSERT_EQ(taille(tab), 4);
            ASSERT_EQ(espace(tab), 8);
            ASSERT_EQ(element(tab, 0), 1);
            ASSERT_EQ(element(tab, 1), 3);
            ASSERT_EQ(element(tab, 2), 2);
            ASSERT_EQ(element(tab, 3), 2);
            detruire(&tab);
        END_TEST

        BEGIN_TESTI("supprimer-non")
            struct tab_t* tab = creer();
            ajouter(tab, 1);
            ajouter(tab, 2);
            ajouter(tab, 3);
            supprimer(tab, 4);
            ASSERT_EQ(taille(tab), 3);
            ASSERT_EQ(espace(tab), 4);
            ASSERT_EQ(element(tab, 0), 1);
            ASSERT_EQ(element(tab, 1), 2);
            ASSERT_EQ(element(tab, 2), 3);
            detruire(&tab);
        END_TEST

        BEGIN_TESTI("supprimer-tout")
            struct tab_t* tab = creer();
            ajouter(tab, 1);
            ajouter(tab, 2);
            ajouter(tab, 3);
            supprimer(tab, 1);
            supprimer(tab, 2);
            supprimer(tab, 3);
            ASSERT_EQ(taille(tab), 0);
            ASSERT_EQ(espace(tab), 4);
            detruire(&tab);
        END_TEST

        BEGIN_TESTI("serrer-1")
            struct tab_t* tab = creer();
            ajouter(tab, 1);
            ajouter(tab, 2);
            ajouter(tab, 3);
            serrer(tab);
            ASSERT_EQ(taille(tab), 3);
            ASSERT_EQ(espace(tab), 3);
            ASSERT_EQ(element(tab, 0), 1);
            ASSERT_EQ(element(tab, 1), 2);
            ASSERT_EQ(element(tab, 2), 3);
            detruire(&tab);
        END_TEST

        BEGIN_TESTI("serrer-0")
            struct tab_t* tab = creer();
            serrer(tab);
            ASSERT_EQ(taille(tab), 0);
            ASSERT_EQ(espace(tab), 4);
            detruire(&tab);
        END_TEST
    
        REPORT_TO_STDOUT
    END_SECTION()

    return 0;
}


