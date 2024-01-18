procedure Date is

    -- Retourne le nombre de jours du mois Mois
    --
    -- Paramètres :
    --    Mois: le mois
    --
    -- Précondition : 1<= Mois <= 12

    function Nombre_De_Jours(Mois: Integer) return Integer with
            Pre => 0<=Mois and then Mois <= 12
    is
        Result: Integer;
        begin
