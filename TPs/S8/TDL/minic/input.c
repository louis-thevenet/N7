test25 {
    typedef struct Point {
        int x;
        int y;
    } Point;
    typedef struct Segment {
        Point ext1;
        Point ext2;
    } Segment;
    typedef struct Triangle {
        Segment s1;
        Segment s2;
        Segment s3;
    } Triangle;

    void prints(int a) {
        int b = a + 5;
        b = 6;
        b = b + 5;
    }

    void printsaa() {
        int a = 5;
        a = a + 5;
    }
    void printsaaa(Segment s) {
    }
}