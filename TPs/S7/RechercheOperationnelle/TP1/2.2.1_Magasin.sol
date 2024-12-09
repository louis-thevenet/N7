Problem:    PbMagasin
Rows:       11
Columns:    12
Non-zeros:  36
Status:     OPTIMAL
Objective:  CoutTotal = 9.5 (MINimum)

   No.   Row name   St   Activity     Lower bound   Upper bound    Marginal
------ ------------ -- ------------- ------------- ------------- -------------
     1 RespectStock[F1,M1]
                    NU           2.5                         2.5            -1 
     2 RespectStock[F1,M2]
                    B            0.5                           1 
     3 RespectStock[F1,M3]
                    B              0                           2 
     4 RespectStock[F2,M1]
                    NU             1                           1            -2 
     5 RespectStock[F2,M2]
                    B              1                           2 
     6 RespectStock[F2,M3]
                    NU             1                           1            -1 
     7 RespectDemande[F1,D1]
                    NS             2             2             =             2 
     8 RespectDemande[F1,D2]
                    NS             1             1             =             2 
     9 RespectDemande[F2,D1]
                    B              0            -0             = 
    10 RespectDemande[F2,D2]
                    NS             3             3             =             3 
    11 CoutTotal    B            9.5                             

   No. Column name  St   Activity     Lower bound   Upper bound    Marginal
------ ------------ -- ------------- ------------- ------------- -------------
     1 D[F1,M1,D1]  B              2             0               
     2 D[F1,M1,D2]  B            0.5             0               
     3 D[F1,M2,D1]  NL             0             0                       < eps
     4 D[F1,M2,D2]  B            0.5             0               
     5 D[F1,M3,D1]  NL             0             0                           1 
     6 D[F1,M3,D2]  NL             0             0                           1 
     7 D[F2,M1,D1]  NL             0             0                           3 
     8 D[F2,M1,D2]  B              1             0               
     9 D[F2,M2,D1]  NL             0             0                           3 
    10 D[F2,M2,D2]  B              1             0               
    11 D[F2,M3,D1]  NL             0             0                           3 
    12 D[F2,M3,D2]  B              1             0               

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
