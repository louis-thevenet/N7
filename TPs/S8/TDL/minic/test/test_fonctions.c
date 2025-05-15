test_fonctions {
    int fonc() {
        int b = 5;
        return b;
    }
    int a = fonc();
    print a;

    int fonc2(int a) { return a; }

    int b = fonc2(a + 5);
    print b;
}