test_pointeurs {
    int i = 1;
    int *p = &i;
    int k = *p;

    print k;  // 1
    print *p; // 1
    print p;  // 0
}