Problem:    PbPreferences
Rows:       7
Columns:    9 (9 integer, 9 binary)
Non-zeros:  27
Status:     INTEGER OPTIMAL
Objective:  SatisfactionTotale = 21 (MAXimum)

   No.   Row name        Activity     Lower bound   Upper bound
------ ------------    ------------- ------------- -------------
     1 RespectDistributionLigne[P1]
                                   1             1             = 
     2 RespectDistributionLigne[P2]
                                   1             1             = 
     3 RespectDistributionLigne[P3]
                                   1             1             = 
     4 RespectDistributionColonne[T1]
                                   1             1             = 
     5 RespectDistributionColonne[T2]
                                   1             1             = 
     6 RespectDistributionColonne[T3]
                                   1             1             = 
     7 SatisfactionTotale
                                  21                             

   No. Column name       Activity     Lower bound   Upper bound
------ ------------    ------------- ------------- -------------
     1 M[P1,T1]     *              1             0             1 
     2 M[P1,T2]     *              0             0             1 
     3 M[P1,T3]     *              0             0             1 
     4 M[P2,T1]     *              0             0             1 
     5 M[P2,T2]     *              1             0             1 
     6 M[P2,T3]     *              0             0             1 
     7 M[P3,T1]     *              0             0             1 
     8 M[P3,T2]     *              0             0             1 
     9 M[P3,T3]     *              1             0             1 

Integer feasibility conditions:

KKT.PE: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

KKT.PB: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

End of output
