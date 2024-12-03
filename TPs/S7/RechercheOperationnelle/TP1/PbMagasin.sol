Problem:    PbMagasin
Rows:       16
Columns:    12
Non-zeros:  36
Status:     OPTIMAL
Objective:  CoutTotal[F1,M1] = 0 (MINimum)

   No.   Row name   St   Activity     Lower bound   Upper bound    Marginal
------ ------------ -- ------------- ------------- ------------- -------------
     1 RespectStock[F1,M1]
                    B              0                         2.5 
     2 RespectStock[F1,M2]
                    NU             1                           1            -1 
     3 RespectStock[F1,M3]
                    NU             2                           2            -1 
     4 RespectStock[F2,M1]
                    B              1                           1 
     5 RespectStock[F2,M2]
                    NU             2                           2         < eps
     6 RespectStock[F2,M3]
                    B              0                           1 
     7 RespectDemande[F1,D1]
                    NS             2             2             =             1 
     8 RespectDemande[F1,D2]
                    NS             1             1             =             1 
     9 RespectDemande[F2,D1]
                    B              0            -0             = 
    10 RespectDemande[F2,D2]
                    NS             3             3             =         < eps
    11 CoutTotal[F1,M1]
                    B              0                             
    12 CoutTotal[F1,M2]
                    B              2                             
    13 CoutTotal[F1,M3]
                    B              6                             
    14 CoutTotal[F2,M1]
                    B              1                             
    15 CoutTotal[F2,M2]
                    B              6                             
    16 CoutTotal[F2,M3]
                    B              0                             

   No. Column name  St   Activity     Lower bound   Upper bound    Marginal
------ ------------ -- ------------- ------------- ------------- -------------
     1 D[F1,M1,D1]  B              0             0               
     2 D[F1,M1,D2]  NL             0             0                       < eps
     3 D[F1,M2,D1]  B              1             0               
     4 D[F1,M2,D2]  NL             0             0                       < eps
     5 D[F1,M3,D1]  B              1             0               
     6 D[F1,M3,D2]  B              1             0               
     7 D[F2,M1,D1]  NL             0             0                       < eps
     8 D[F2,M1,D2]  B              1             0               
     9 D[F2,M2,D1]  NL             0             0                       < eps
    10 D[F2,M2,D2]  B              2             0               
    11 D[F2,M3,D1]  NL             0             0                       < eps
    12 D[F2,M3,D2]  NL             0             0                       < eps

Karush-Kuhn-Tucker optimality conditions:

KKT.PE: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

KKT.PB: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

KKT.DE: max.abs.err = 0.00e+00 on column 0
        max.rel.err = 0.00e+00 on column 0
        High quality

KKT.DB: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

End of output
