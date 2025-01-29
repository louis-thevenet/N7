-------- MODULE hlmc -------

    VARIABLES h, m, c, l
    RIVES == {"G", "D"}

    Inv(r) ==
        IF r = "G"
            THEN "D"
            ELSE "G"

    TypeInvariant == {h, l, m,c} \subseteq RIVES

    Init ==
        /\ h = "G"
        /\ l = "G"
        /\ m = "G"
        /\ c = "G"
        (*/\ PasMiam*)

    PasMiam ==
        /\ (l = m => h = m)
        /\ (c = m => h = m)

    MoveH == 
        /\ h' = Inv(h)
        /\ UNCHANGED <<l, m, c>>
        /\ PasMiam' 

    MoveHL ==
        /\ h' = Inv(h)
        /\ l' = Inv(l)
        /\ h = l
        /\ UNCHANGED << m, c >>
        /\ PasMiam'

    MoveHM ==
        /\ h' = Inv(h)
        /\ m' = Inv(m)
        /\ h = m
        /\ UNCHANGED << l, c >>
        /\ PasMiam'

    MoveHC ==
        /\ h' = Inv(h)
        /\ c' = Inv(c)
        /\ h = c
        /\ UNCHANGED << l, m >>
        /\ PasMiam'

    Next ==
        \/ MoveH
        \/ MoveHL
        \/ MoveHM
        \/ MoveHC

    Spec ==
        /\ Init
        /\ [Next]_<<h,l,m,c>>
    
    But == {h,l,m,c} = {"D"}
==================================================
