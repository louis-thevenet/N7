Problem:    Pb2
Rows:       61
Columns:    42 (36 integer, 36 binary)
Non-zeros:  210
Status:     INTEGER EMPTY
Objective:  CoutTotal = 0 (MINimum)

   No.   Row name        Activity     Lower bound   Upper bound
------ ------------    ------------- ------------- -------------
     1 TousClientsServisUneFois[Alpha]
                                   0             1             = 
     2 TousClientsServisUneFois[C1]
                                   0             1             = 
     3 TousClientsServisUneFois[C2]
                                   0             1             = 
     4 TousClientsServisUneFois[C3]
                                   0             1             = 
     5 TousClientsServisUneFois[C4]
                                   0             1             = 
     6 TousClientsServisUneFois[C5]
                                   0             1             = 
     7 TousClientsQuittesUneFois[Alpha]
                                   0             1             = 
     8 TousClientsQuittesUneFois[C1]
                                   0             1             = 
     9 TousClientsQuittesUneFois[C2]
                                   0             1             = 
    10 TousClientsQuittesUneFois[C3]
                                   0             1             = 
    11 TousClientsQuittesUneFois[C4]
                                   0             1             = 
    12 TousClientsQuittesUneFois[C5]
                                   0             1             = 
    13 UneFoisParClient[Alpha]
                                   0            -0             = 
    14 UneFoisParClient[C1]
                                   0            -0             = 
    15 UneFoisParClient[C2]
                                   0            -0             = 
    16 UneFoisParClient[C3]
                                   0            -0             = 
    17 UneFoisParClient[C4]
                                   0            -0             = 
    18 UneFoisParClient[C5]
                                   0            -0             = 
    19 PasDeDetour[Alpha]
                                   0             2               
    20 PasDeDetour[C1]
                                   0             2               
    21 PasDeDetour[C2]
                                   0             2               
    22 PasDeDetour[C3]
                                   0             2               
    23 PasDeDetour[C4]
                                   0             2               
    24 PasDeDetour[C5]
                                   0             2               
    25 PasDeDetour2[Alpha,Alpha]
                                   0                           4 
    26 PasDeDetour2[Alpha,C1]
                                   0                           4 
    27 PasDeDetour2[Alpha,C2]
                                   0                           4 
    28 PasDeDetour2[Alpha,C3]
                                   0                           4 
    29 PasDeDetour2[Alpha,C4]
                                   0                           4 
    30 PasDeDetour2[Alpha,C5]
                                   0                           4 
    31 PasDeDetour2[C1,Alpha]
                                   0                           4 
    32 PasDeDetour2[C1,C1]
                                   0                           4 
    33 PasDeDetour2[C1,C2]
                                   0                           4 
    34 PasDeDetour2[C1,C3]
                                   0                           4 
    35 PasDeDetour2[C1,C4]
                                   0                           4 
    36 PasDeDetour2[C1,C5]
                                   0                           4 
    37 PasDeDetour2[C2,Alpha]
                                   0                           4 
    38 PasDeDetour2[C2,C1]
                                   0                           4 
    39 PasDeDetour2[C2,C2]
                                   0                           4 
    40 PasDeDetour2[C2,C3]
                                   0                           4 
    41 PasDeDetour2[C2,C4]
                                   0                           4 
    42 PasDeDetour2[C2,C5]
                                   0                           4 
    43 PasDeDetour2[C3,Alpha]
                                   0                           4 
    44 PasDeDetour2[C3,C1]
                                   0                           4 
    45 PasDeDetour2[C3,C2]
                                   0                           4 
    46 PasDeDetour2[C3,C3]
                                   0                           4 
    47 PasDeDetour2[C3,C4]
                                   0                           4 
    48 PasDeDetour2[C3,C5]
                                   0                           4 
    49 PasDeDetour2[C4,Alpha]
                                   0                           4 
    50 PasDeDetour2[C4,C1]
                                   0                           4 
    51 PasDeDetour2[C4,C2]
                                   0                           4 
    52 PasDeDetour2[C4,C3]
                                   0                           4 
    53 PasDeDetour2[C4,C4]
                                   0                           4 
    54 PasDeDetour2[C4,C5]
                                   0                           4 
    55 PasDeDetour2[C5,Alpha]
                                   0                           4 
    56 PasDeDetour2[C5,C1]
                                   0                           4 
    57 PasDeDetour2[C5,C2]
                                   0                           4 
    58 PasDeDetour2[C5,C3]
                                   0                           4 
    59 PasDeDetour2[C5,C4]
                                   0                           4 
    60 PasDeDetour2[C5,C5]
                                   0                           4 
    61 CoutTotal                   0                             

   No. Column name       Activity     Lower bound   Upper bound
------ ------------    ------------- ------------- -------------
     1 M[Alpha,Alpha]
                    *              0             0             1 
     2 M[Alpha,C1]  *              0             0             1 
     3 M[Alpha,C2]  *              0             0             1 
     4 M[Alpha,C3]  *              0             0             1 
     5 M[Alpha,C4]  *              0             0             1 
     6 M[Alpha,C5]  *              0             0             1 
     7 M[C1,Alpha]  *              0             0             1 
     8 M[C1,C1]     *              0             0             1 
     9 M[C1,C2]     *              0             0             1 
    10 M[C1,C3]     *              0             0             1 
    11 M[C1,C4]     *              0             0             1 
    12 M[C1,C5]     *              0             0             1 
    13 M[C2,Alpha]  *              0             0             1 
    14 M[C2,C1]     *              0             0             1 
    15 M[C2,C2]     *              0             0             1 
    16 M[C2,C3]     *              0             0             1 
    17 M[C2,C4]     *              0             0             1 
    18 M[C2,C5]     *              0             0             1 
    19 M[C3,Alpha]  *              0             0             1 
    20 M[C3,C1]     *              0             0             1 
    21 M[C3,C2]     *              0             0             1 
    22 M[C3,C3]     *              0             0             1 
    23 M[C3,C4]     *              0             0             1 
    24 M[C3,C5]     *              0             0             1 
    25 M[C4,Alpha]  *              0             0             1 
    26 M[C4,C1]     *              0             0             1 
    27 M[C4,C2]     *              0             0             1 
    28 M[C4,C3]     *              0             0             1 
    29 M[C4,C4]     *              0             0             1 
    30 M[C4,C5]     *              0             0             1 
    31 M[C5,Alpha]  *              0             0             1 
    32 M[C5,C1]     *              0             0             1 
    33 M[C5,C2]     *              0             0             1 
    34 M[C5,C3]     *              0             0             1 
    35 M[C5,C4]     *              0             0             1 
    36 M[C5,C5]     *              0             0             1 
    37 u[Alpha]                    0                             
    38 u[C1]                       0                             
    39 u[C2]                       0                             
    40 u[C3]                       0                             
    41 u[C4]                       0                             
    42 u[C5]                       0                             

Integer feasibility conditions:

KKT.PE: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

KKT.PB: max.abs.err = 2.00e+00 on row 19
        max.rel.err = 6.67e-01 on row 19
        SOLUTION IS INFEASIBLE

End of output
