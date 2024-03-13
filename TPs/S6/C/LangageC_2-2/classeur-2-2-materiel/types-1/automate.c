#include "automate.h"

// États possibles de l'automate, modélisé par une énumération (cachée)
enum mode_t {
    ON = 0, OFF, INCONNU
};

// État interne de l'automate (initialement, état inconnu, ni on ni off)
static enum mode_t etat = INCONNU;

void on() {
    etat = ON;
}

void off() {
    etat = OFF;
}

bool is_on() {
    return (etat == ON);
}



