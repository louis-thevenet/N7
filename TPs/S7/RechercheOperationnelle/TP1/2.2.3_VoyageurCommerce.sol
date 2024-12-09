Problem:    Pb2
Rows:       61
Columns:    42 (42 integer, 36 binary)
Non-zeros:  210
Status:     INTEGER OPTIMAL
Objective:  DistanceTotale = 6 (MINimum)

   No.   Row name        Activity     Lower bound   Upper bound
------ ------------    ------------- ------------- -------------
     1 TousClientsServisUneFois[Alpha]
                                   1             1             = 
     2 TousClientsServisUneFois[C1]
                                   1             1             = 
     3 TousClientsServisUneFois[C2]
                                   1             1             = 
     4 TousClientsServisUneFois[C3]
                                   1             1             = 
     5 TousClientsServisUneFois[C4]
                                   1             1             = 
     6 TousClientsServisUneFois[C5]
                                   1             1             = 
     7 TousClientsQuittesUneFois[Alpha]
                                   1             1             = 
     8 TousClientsQuittesUneFois[C1]
                                   1             1             = 
     9 TousClientsQuittesUneFois[C2]
                                   1             1             = 
    10 TousClientsQuittesUneFois[C3]
                                   1             1             = 
    11 TousClientsQuittesUneFois[C4]
                                   1             1             = 
    12 TousClientsQuittesUneFois[C5]
                                   1             1             = 
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
    19 ordrePositif[Alpha]
                                   0            -0               
    20 ordrePositif[C1]
                                   0            -0               
    21 ordrePositif[C2]
                                   0            -0               
    22 ordrePositif[C3]
                                   0            -0               
    23 ordrePositif[C4]
                                   0            -0               
    24 ordrePositif[C5]
                                   0            -0               
    25 PasDeDetour[Alpha,Alpha]
                                   0                       99999 
    26 PasDeDetour[Alpha,C1]
                              100000                       99999 
    27 PasDeDetour[Alpha,C2]
                                   0                       99999 
    28 PasDeDetour[Alpha,C3]
                                   0                       99999 
    29 PasDeDetour[Alpha,C4]
                                   0                       99999 
    30 PasDeDetour[Alpha,C5]
                                   0                       99999 
    31 PasDeDetour[C1,Alpha]
                                   0                       99999 
    32 PasDeDetour[C1,C1]
                                   0                       99999 
    33 PasDeDetour[C1,C2]
                              100000                       99999 
    34 PasDeDetour[C1,C3]
                                   0                       99999 
    35 PasDeDetour[C1,C4]
                                   0                       99999 
    36 PasDeDetour[C1,C5]
                                   0                       99999 
    37 PasDeDetour[C2,Alpha]
                              100000                       99999 
    38 PasDeDetour[C2,C1]
                                   0                       99999 
    39 PasDeDetour[C2,C2]
                                   0                       99999 
    40 PasDeDetour[C2,C3]
                                   0                       99999 
    41 PasDeDetour[C2,C4]
                                   0                       99999 
    42 PasDeDetour[C2,C5]
                                   0                       99999 
    43 PasDeDetour[C3,Alpha]
                                   0                       99999 
    44 PasDeDetour[C3,C1]
                                   0                       99999 
    45 PasDeDetour[C3,C2]
                                   0                       99999 
    46 PasDeDetour[C3,C3]
                                   0                       99999 
    47 PasDeDetour[C3,C4]
                              100000                       99999 
    48 PasDeDetour[C3,C5]
                                   0                       99999 
    49 PasDeDetour[C4,Alpha]
                                   0                       99999 
    50 PasDeDetour[C4,C1]
                                   0                       99999 
    51 PasDeDetour[C4,C2]
                                   0                       99999 
    52 PasDeDetour[C4,C3]
                                   0                       99999 
    53 PasDeDetour[C4,C4]
                                   0                       99999 
    54 PasDeDetour[C4,C5]
                              100000                       99999 
    55 PasDeDetour[C5,Alpha]
                                   0                       99999 
    56 PasDeDetour[C5,C1]
                                   0                       99999 
    57 PasDeDetour[C5,C2]
                                   0                       99999 
    58 PasDeDetour[C5,C3]
                              100000                       99999 
    59 PasDeDetour[C5,C4]
                                   0                       99999 
    60 PasDeDetour[C5,C5]
                                   0                       99999 
    61 DistanceTotale
                                   6                             

   No. Column name       Activity     Lower bound   Upper bound
------ ------------    ------------- ------------- -------------
     1 M[Alpha,Alpha]
                    *              0             0             1 
     2 M[Alpha,C1]  *              1             0             1 
     3 M[Alpha,C2]  *              0             0             1 
     4 M[Alpha,C3]  *              0             0             1 
     5 M[Alpha,C4]  *              0             0             1 
     6 M[Alpha,C5]  *              0             0             1 
     7 M[C1,Alpha]  *              0             0             1 
     8 M[C1,C1]     *              0             0             1 
     9 M[C1,C2]     *              1             0             1 
    10 M[C1,C3]     *              0             0             1 
    11 M[C1,C4]     *              0             0             1 
    12 M[C1,C5]     *              0             0             1 
    13 M[C2,Alpha]  *              1             0             1 
    14 M[C2,C1]     *              0             0             1 
    15 M[C2,C2]     *              0             0             1 
    16 M[C2,C3]     *              0             0             1 
    17 M[C2,C4]     *              0             0             1 
    18 M[C2,C5]     *              0             0             1 
    19 M[C3,Alpha]  *              0             0             1 
    20 M[C3,C1]     *              0             0             1 
    21 M[C3,C2]     *              0             0             1 
    22 M[C3,C3]     *              0             0             1 
    23 M[C3,C4]     *              1             0             1 
    24 M[C3,C5]     *              0             0             1 
    25 M[C4,Alpha]  *              0             0             1 
    26 M[C4,C1]     *              0             0             1 
    27 M[C4,C2]     *              0             0             1 
    28 M[C4,C3]     *              0             0             1 
    29 M[C4,C4]     *              0             0             1 
    30 M[C4,C5]     *              1             0             1 
    31 M[C5,Alpha]  *              0             0             1 
    32 M[C5,C1]     *              0             0             1 
    33 M[C5,C2]     *              0             0             1 
    34 M[C5,C3]     *              1             0             1 
    35 M[C5,C4]     *              0             0             1 
    36 M[C5,C5]     *              0             0             1 
    37 u[Alpha]     *              0                             
    38 u[C1]        *              0                             
    39 u[C2]        *              0                             
    40 u[C3]        *              0                             
    41 u[C4]        *              0                             
    42 u[C5]        *              0                             

Integer feasibility conditions:

KKT.PE: max.abs.err = 0.00e+00 on row 0
        max.rel.err = 0.00e+00 on row 0
        High quality

KKT.PB: max.abs.err = 1.00e+00 on row 26
        max.rel.err = 1.00e-05 on row 26
        Low quality

End of output
