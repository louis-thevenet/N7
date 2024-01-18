/**************************************************************
 * Batterie de tests unitaires pour le module complexe.
 * /!\ NE PAS MODIFIER /!\
 *
 * @author G. Dupont <guillaume.dupont@toulouse-inp.fr>
 **************************************************************/
#include "complexe.h"
#include "tests.h"
#include <math.h>

#define PRECISION   1e-6

int main() {
    INITIALIZE_TESTS();
    SET_ANALYSIS("resultat.csv");

    BEGIN_SECTION("base");
        BEGIN_TESTI("init");
        complexe_t c;
        init(&c, 1.0, 2.0);
        ASSERT_EQ_F(reelle(c)    , 1.0, PRECISION);
        ASSERT_EQ_F(imaginaire(c), 2.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("set_reelle");
        complexe_t c;
        init(&c, 7.0, -4.5);
        set_reelle(&c, 5.0);
        ASSERT_EQ_F(reelle(c)    ,  5.0, PRECISION);
        ASSERT_EQ_F(imaginaire(c), -4.5, PRECISION);
        END_TEST;

        BEGIN_TESTI("set_imaginaire");
        complexe_t c;
        init(&c, -131.3, 2723.4);
        set_imaginaire(&c, 99.99);
        ASSERT_EQ_F(reelle(c)    , -131.3 , PRECISION);
        ASSERT_EQ_F(imaginaire(c),   99.99, PRECISION);
        END_TEST;

        BEGIN_TESTI("copie");
        complexe_t c1, c2;
        init(&c1, 125.7 , -981.8);
        init(&c2,  12.63,   71.63);
        copie(&c2, c1);
        ASSERT_EQ_F(reelle(c1)    ,  125.7, PRECISION);
        ASSERT_EQ_F(imaginaire(c1), -981.8, PRECISION);
        ASSERT_EQ_F(reelle(c2)    ,  125.7, PRECISION);
        ASSERT_EQ_F(imaginaire(c2), -981.8, PRECISION);
        END_TEST;

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION();

    BEGIN_SECTION("conjugue");
        BEGIN_TESTI("conjugue-nominal-1");
        complexe_t c, cbar;
        init(&c, 3.5, 7.4);
        init(&cbar, 121.1, 232.2);
        conjugue(&cbar, c);
        ASSERT_EQ_F(reelle(c)       ,  3.5, PRECISION);
        ASSERT_EQ_F(imaginaire(c)   ,  7.4, PRECISION);
        ASSERT_EQ_F(reelle(cbar)    ,  3.5, PRECISION);
        ASSERT_EQ_F(imaginaire(cbar), -7.4, PRECISION);
        END_TEST;

        BEGIN_TESTI("conjugue-nominal-2");
        complexe_t c, cbar;
        init(&c, -1.7, -3.7);
        init(&cbar, -11.1, -22.2);
        conjugue(&cbar, c);
        ASSERT_EQ_F(reelle(c)       , -1.7, PRECISION);
        ASSERT_EQ_F(imaginaire(c)   , -3.7, PRECISION);
        ASSERT_EQ_F(reelle(cbar)    , -1.7, PRECISION);
        ASSERT_EQ_F(imaginaire(cbar),  3.7, PRECISION);
        END_TEST;

        BEGIN_TESTI("conjugue-imag-nul");
        complexe_t c, cbar;
        init(&c, 5.7, 0.0);
        init(&cbar, 9.9, 8.8);
        conjugue(&cbar, c);
        ASSERT_EQ_F(reelle(c)       , 5.7, PRECISION);
        ASSERT_EQ_F(imaginaire(c)   , 0.0, PRECISION);
        ASSERT_EQ_F(reelle(cbar)    , 5.7, PRECISION);
        ASSERT_EQ_F(imaginaire(cbar), 0.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("conjugue-disp");
        complexe_t c;
        init(&c, -13.0, -15.0);
        conjugue(&c, c);
        ASSERT_EQ_F(reelle(c)    , -13.0, PRECISION);
        ASSERT_EQ_F(imaginaire(c),  15.0, PRECISION);
        END_TEST;

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION();

    BEGIN_SECTION("ajouter");
        BEGIN_TESTI("ajouter-nominal-1");
        complexe_t ca, cb, cresult;
        init(&ca, 1.0, 3.5);
        init(&cb, 2.5, 6.5);
        init(&cresult, 3.3, 3.3);
        ajouter(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         ,  1.0, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,  3.5, PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,  2.5, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,  6.5, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    ,  3.5, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult), 10.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("ajouter-nominal-2");
        complexe_t ca, cb, cresult;
        init(&ca, -11.0,  6.3);
        init(&cb,   5.7, -5.2);
        init(&cresult, 1.1, -1.0);
        ajouter(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         , -11.0, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,   6.3, PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,   5.7, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,  -5.2, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    ,  -5.3, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),   1.1, PRECISION);
        END_TEST;

        BEGIN_TESTI("ajouter-zero-1");
        complexe_t ca, cb, cresult;
        init(&ca, 7.6, 0.0);
        init(&cb, 0.0, 3.4);
        init(&cresult, 1.0, 0.1);
        ajouter(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         , 7.6, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     , 0.0, PRECISION);
        ASSERT_EQ_F(reelle(cb)         , 0.0, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     , 3.4, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , 7.6, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult), 3.4, PRECISION);
        END_TEST;

        BEGIN_TESTI("ajouter-zero-2");
        complexe_t ca, cb, cresult;
        init(&ca, -3.1, 2.5);
        init(&cb, 0.0, 0.0);
        init(&cresult, 10.0, 10.0);
        ajouter(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         , -3.1, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,  2.5, PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,  0.0, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,  0.0, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , -3.1, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  2.5, PRECISION);
        END_TEST;

        BEGIN_TESTI("ajouter-disp-1");
        complexe_t ca, cb;
        init(&ca, 1.2, 1.3);
        init(&cb, 1.4, 1.5);
        ajouter(&ca, ca, cb);
        ASSERT_EQ_F(reelle(ca)    , 2.6, PRECISION);
        ASSERT_EQ_F(imaginaire(ca), 2.8, PRECISION);
        ASSERT_EQ_F(reelle(cb)    , 1.4, PRECISION);
        ASSERT_EQ_F(imaginaire(cb), 1.5, PRECISION);
        END_TEST;

        BEGIN_TESTI("ajouter-disp-2");
        complexe_t ca, cb;
        init(&ca, 2.2, 2.3);
        init(&cb, 2.4, 2.5);
        ajouter(&cb, ca, cb);
        ASSERT_EQ_F(reelle(ca)    , 2.2, PRECISION);
        ASSERT_EQ_F(imaginaire(ca), 2.3, PRECISION);
        ASSERT_EQ_F(reelle(cb    ), 4.6, PRECISION);
        ASSERT_EQ_F(imaginaire(cb), 4.8, PRECISION);
        END_TEST;

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION();

    BEGIN_SECTION("soustraire");
        BEGIN_TESTI("soustraire-nominal-1");
        complexe_t ca, cb, cresult;
        init(&ca, 3.5, 3.5);
        init(&cb, 2.5, 1.5);
        init(&cresult, 4.4, 4.4);
        soustraire(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         , 3.5, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     , 3.5, PRECISION);
        ASSERT_EQ_F(reelle(cb)         , 2.5, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     , 1.5, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , 1.0, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult), 2.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("soustraire-nominal-2");
        complexe_t ca, cb, cresult;
        init(&ca, -5.0, 3.1);
        init(&cb, 4.5, -2.3);
        init(&cresult, 0.5, -11.1);
        soustraire(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         , -5.0, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,  3.1, PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,  4.5, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     , -2.3, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , -9.5, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  5.4, PRECISION);
        END_TEST;

        BEGIN_TESTI("soustraire-zero-1");
        complexe_t ca, cb, cresult;
        init(&ca, 0.0, 0.0);
        init(&cb, 6.1, 2.3);
        init(&cresult, 1.0, 0.0);
        soustraire(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         ,  0.0, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,  0.0, PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,  6.1, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,  2.3, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , -6.1, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult), -2.3, PRECISION);
        END_TEST;

        BEGIN_TESTI("soustraire-zero-2");
        complexe_t ca, cb, cresult;
        init(&ca, -7.117, 3.551);
        init(&cb, 0.0, 0.0);
        init(&cresult, 10.0, 10.0);
        soustraire(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         , -7.117, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,  3.551, PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,  0.0  , PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,  0.0  , PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , -7.117, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  3.551, PRECISION);
        END_TEST;

        BEGIN_TESTI("soustraire-disp-1");
        complexe_t ca, cb;
        init(&ca, 3.2, 3.3);
        init(&cb, 3.4, 3.6);
        soustraire(&ca, ca, cb);
        ASSERT_EQ_F(reelle(ca)    , -0.2, PRECISION);
        ASSERT_EQ_F(imaginaire(ca), -0.3, PRECISION);
        ASSERT_EQ_F(reelle(cb)    ,  3.4, PRECISION);
        ASSERT_EQ_F(imaginaire(cb),  3.6, PRECISION);
        END_TEST;

        BEGIN_TESTI("soustraire-disp-2");
        complexe_t ca, cb;
        init(&ca, 4.4, 4.3);
        init(&cb, 4.1, 4.5);
        soustraire(&cb, ca, cb);
        ASSERT_EQ_F(reelle(ca)    ,  4.4, PRECISION);
        ASSERT_EQ_F(imaginaire(ca),  4.3, PRECISION);
        ASSERT_EQ_F(reelle(cb)    ,  0.3, PRECISION);
        ASSERT_EQ_F(imaginaire(cb), -0.2, PRECISION);
        END_TEST;

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION();

    BEGIN_SECTION("multiplier");
        BEGIN_TESTI("multiplier-nominal-1");
        complexe_t ca, cb, cresult;
        init(&ca, 2.1, 3.7);
        init(&cb, 4.6, 3.8);
        init(&cresult, 3.1, 3.1);
        multiplier(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         ,   2.1, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,   3.7, PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,   4.6, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,   3.8, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , - 4.4, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  25.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("multiplier-nominal-2");
        complexe_t ca, cb, cresult;
        init(&ca, -1.2,  7.4);
        init(&cb,  8.9, -5.6);
        init(&cresult, -5.0, 1.1);
        multiplier(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         , - 1.2 , PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,   7.4 , PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,   8.9 , PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     , - 5.6 , PRECISION);
        ASSERT_EQ_F(reelle(cresult)    ,  30.76, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  72.58, PRECISION);
        END_TEST;

        BEGIN_TESTI("multiplier-nominal-3");
        complexe_t ca, cb, cresult;
        init(&ca,  1.6, -2.6);
        init(&cb,  1.4,  2.4);
        init(&cresult, -7.0, -3.9);
        multiplier(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         ,   1.6 , PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     , - 2.6 , PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,   1.4 , PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,   2.4 , PRECISION);
        ASSERT_EQ_F(reelle(cresult)    ,   8.48, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),   0.2 , PRECISION);
        END_TEST;

        BEGIN_TESTI("multiplier-reel-1");
        complexe_t ca, cb, cresult;
        init(&ca,  2.0,  0.0);
        init(&cb, 11.2, 15.7);
        init(&cresult, -1.0, 0.3);
        multiplier(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         ,  2.0, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,  0.0, PRECISION);
        ASSERT_EQ_F(reelle(cb)         , 11.2, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     , 15.7, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , 22.4, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult), 31.4, PRECISION);
        END_TEST;

        BEGIN_TESTI("multiplier-reel-2");
        complexe_t ca, cb, cresult;
        init(&ca, -5.7, 3.1);
        init(&cb, -4.0, 0.0);
        init(&cresult, 0.7, 0.6);
        multiplier(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         , - 5.7, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,   3.1, PRECISION);
        ASSERT_EQ_F(reelle(cb)         , - 4.0, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,   0.0, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    ,  22.8, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult), -12.4, PRECISION);
        END_TEST;

        BEGIN_TESTI("multiplier-imaginaire-1");
        complexe_t ca, cb, cresult;
        init(&ca,  0.0, -3.0);
        init(&cb, -1.1,  2.4);
        init(&cresult, 0.5, 0.5);
        multiplier(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         ,  0.0, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     , -3.0, PRECISION);
        ASSERT_EQ_F(reelle(cb)         , -1.1, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,  2.4, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    ,  7.2, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  3.3, PRECISION);
        END_TEST;

        BEGIN_TESTI("multiplier-imaginaire-2");
        complexe_t ca, cb, cresult;
        init(&ca, 5.1, 6.2);
        init(&cb, 0.0, 1.5);
        init(&cresult, 0.6, 0.6);
        multiplier(&cresult, ca, cb);
        ASSERT_EQ_F(reelle(ca)         ,  5.1 , PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,  6.2 , PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,  0.0 , PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,  1.5 , PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , -9.3 , PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  7.65, PRECISION);
        END_TEST;

        BEGIN_TESTI("multiplier-disp-1");
        complexe_t ca, cb;
        init(&ca,  7.3, 1.5);
        init(&cb, -2.2, 2.6);
        multiplier(&ca, ca, cb);
        ASSERT_EQ_F(reelle(ca)         , -19.96, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,  15.68, PRECISION);
        ASSERT_EQ_F(reelle(cb)         , - 2.2 , PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     ,   2.6 , PRECISION);
        END_TEST;

        BEGIN_TESTI("multiplier-disp-2");
        complexe_t ca, cb;
        init(&ca, 3.4, -5.6);
        init(&cb, 1.3,  0.2);
        multiplier(&cb, ca, cb);
        ASSERT_EQ_F(reelle(ca)         ,  3.4 , PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     , -5.6 , PRECISION);
        ASSERT_EQ_F(reelle(cb)         ,  5.54, PRECISION);
        ASSERT_EQ_F(imaginaire(cb)     , -6.6 , PRECISION);
        END_TEST;

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION();

    BEGIN_SECTION("echelle");
        BEGIN_TESTI("echelle-nominal-1");
        complexe_t ca, cresult;
        init(&ca, 12.0, 3.0);
        init(&cresult, 0.1, 0.2);
        echelle(&cresult, ca, 2.0);
        ASSERT_EQ_F(reelle(ca)         , 12.0, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,  3.0, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , 24.0, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  6.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("echelle-nominal-2");
        complexe_t ca, cresult;
        init(&ca, -7.0, 2.1);
        init(&cresult, 0.1, 0.2);
        echelle(&cresult, ca, -3.0);
        ASSERT_EQ_F(reelle(ca)         , - 7.0, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     ,   2.1, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    ,  21.0, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult), - 6.3, PRECISION);
        END_TEST;

        BEGIN_TESTI("echelle-0");
        complexe_t ca, cresult;
        init(&ca, 5.0, -1.0);
        init(&cresult, 1.1, 1.1);
        echelle(&cresult, ca, 0.0);
        ASSERT_EQ_F(reelle(ca)         ,  5.0, PRECISION);
        ASSERT_EQ_F(imaginaire(ca)     , -1.0, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    ,  0.0, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  0.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("echelle-disp");
        complexe_t c;
        init(&c, -9.8, -7.3);
        echelle(&c, c, 1.5);
        ASSERT_EQ_F(reelle(c)    , -14.7 , PRECISION);
        ASSERT_EQ_F(imaginaire(c), -10.95, PRECISION);
        END_TEST;

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION();

    BEGIN_SECTION("puissance");
        BEGIN_TESTI("puissance-nominal-1");
        complexe_t c, cresult;
        init(&c, 1.0, 1.0);
        init(&cresult, -0.1, 5.5);
        puissance(&cresult, c, 4);
        ASSERT_EQ_F(reelle(c)          ,  1.0, PRECISION);
        ASSERT_EQ_F(imaginaire(c)      ,  1.0, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , -4.0, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  0.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("puissance-nominal-2");
        complexe_t c, cresult;
        init(&c, -1.5, 2.5);
        init(&cresult, 3.3, -4.1);
        puissance(&cresult, c, 7);
        ASSERT_EQ_F(reelle(c)          , -   1.5   , PRECISION);
        ASSERT_EQ_F(imaginaire(c)      ,     2.5   , PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , -1071.1875, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  1434.6875, PRECISION);
        END_TEST;

        BEGIN_TESTI("puissance-0");
        complexe_t c, cresult;
        init(&c, 7.1, -8.3);
        init(&cresult, 0.1, 0.2);
        puissance(&cresult, c, 0);
        ASSERT_EQ_F(reelle(c)          ,  7.1, PRECISION);
        ASSERT_EQ_F(imaginaire(c)      , -8.3, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    ,  1.0, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  0.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("puissance-1");
        complexe_t c, cresult;
        init(&c, -7.1, 8.3);
        init(&cresult, 0.2, 0.1);
        puissance(&cresult, c, 1);
        ASSERT_EQ_F(reelle(c)          , -7.1, PRECISION);
        ASSERT_EQ_F(imaginaire(c)      ,  8.3, PRECISION);
        ASSERT_EQ_F(reelle(cresult)    , -7.1, PRECISION);
        ASSERT_EQ_F(imaginaire(cresult),  8.3, PRECISION);
        END_TEST;

        BEGIN_TESTI("puissance-disp");
        complexe_t c;
        init(&c, 2.0, 3.0);
        puissance(&c, c, 3);
        ASSERT_EQ_F(reelle(c)   , -46.0, PRECISION);
        ASSERT_EQ_F(imaginaire(c),  9.0, PRECISION);
        END_TEST;

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION();

    BEGIN_SECTION("module");
        BEGIN_TESTI("module-carre-nominal-1");
        complexe_t c;
        init(&c, 2.0, 3.0);
        double r = module_carre(c);
        ASSERT_EQ_F(r, 13.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("module-carre-nominal-2");
        complexe_t c;
        init(&c, -5.0, 4.0);
        double r = module_carre(c);
        ASSERT_EQ_F(r, 41.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("module-carre-0");
        complexe_t c;
        init(&c, 0.0, 0.0);
        double r = module_carre(c);
        ASSERT_EQ_F(r, 0.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("module-nominal-1");
        complexe_t c;
        init(&c, 3.0, 4.0);
        double r = module(c);
        ASSERT_EQ_F(r, 5.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("module-nominal-2");
        complexe_t c;
        init(&c, -28.0, -45.0);
        double r = module(c);
        ASSERT_EQ_F(r, 53.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("module-0");
        complexe_t c;
        init(&c, 0.0, 0.0);
        double r = module(c);
        ASSERT_EQ_F(r, 0.0, PRECISION);
        END_TEST;

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION();

    BEGIN_SECTION("argument");
        BEGIN_TESTI("argument-nominal-1");
        complexe_t c;
        init(&c, 2.0, 2.0);
        double r = argument(c);
        ASSERT_EQ_F(r, M_PI / 4.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("argument-nominal-2");
        complexe_t c;
        init(&c, -5.0, 3.0);
        double r = argument(c);
        ASSERT_EQ_F(r, 2.6011732, PRECISION);
        END_TEST;

        BEGIN_TESTI("argument-reel");
        complexe_t c;
        init(&c, 2.0, 0.0);
        double r = argument(c);
        ASSERT_EQ_F(r, 0.0, PRECISION);
        END_TEST;

        BEGIN_TESTI("argument-reel-negatif");
        complexe_t c;
        init(&c, -0.2, 0.0);
        double r = argument(c);
        ASSERT_EQ_F(r, M_PI, PRECISION);
        END_TEST;

        BEGIN_TESTI("argument-imaginaire");
        complexe_t c;
        init(&c, 0.0, 5.0);
        double r = argument(c);
        ASSERT_EQ_F(r, M_PI / 2.0, PRECISION);
        END_TEST;

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION();

    END_ANALYSIS;

    return 0;
}


