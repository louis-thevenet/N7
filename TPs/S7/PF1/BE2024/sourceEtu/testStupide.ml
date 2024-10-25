open Intuitive
open Encodage
open StructureDonnees

module IntuitiveStupideS (S : StructureDonnees) = struct
  module IntuitiveStupide = Intuitive (Stupide) (S)

  (* Tests de encoder_lettre *)
  let%test _ = IntuitiveStupide.encoder_lettre 'a' = 2
  let%test _ = IntuitiveStupide.encoder_lettre 'b' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'c' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'd' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'e' = 2
  let%test _ = IntuitiveStupide.encoder_lettre 'f' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'g' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'h' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'i' = 2
  let%test _ = IntuitiveStupide.encoder_lettre 'j' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'k' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'l' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'm' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'n' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'o' = 2
  let%test _ = IntuitiveStupide.encoder_lettre 'p' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'q' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'r' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 's' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 't' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'u' = 2
  let%test _ = IntuitiveStupide.encoder_lettre 'v' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'w' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'x' = 3
  let%test _ = IntuitiveStupide.encoder_lettre 'y' = 2
  let%test _ = IntuitiveStupide.encoder_lettre 'z' = 3
  let%test _ = IntuitiveStupide.encoder_lettre '&' = 0

  (* Tests de encoder_mot *)
  let%test _ = IntuitiveStupide.encoder_mot "" = []
  let%test _ = IntuitiveStupide.encoder_mot "a" = [ 2 ]
  let%test _ = IntuitiveStupide.encoder_mot "bonjour" = [ 3; 2; 3; 3; 2; 2; 3 ]

  let%test _ =
    IntuitiveStupide.encoder_mot "bonjour!" = [ 3; 2; 3; 3; 2; 2; 3; 0 ]

  let%test _ = IntuitiveStupide.encoder_mot "ocaml" = [ 2; 3; 2; 3; 3 ]
  let dico_fr_stupide = IntuitiveStupide.creer_dico "dico_fr.txt"

  (* Tests de decoder_mot *)
  let%test _ =
    IntuitiveStupide.decoder_mot [ 2; 2; 2 ] dico_fr_stupide
    = [ "yue"; "oui"; "oie"; "eau"; "eao"; "aie" ]

  let%test _ =
    IntuitiveStupide.decoder_mot [ 3; 3; 3; 3 ] dico_fr_stupide
    = [
        "tvhd";
        "ssbs";
        "sprl";
        "slbm";
        "sgml";
        "sgbd";
        "ppcm";
        "pgcd";
        "ntsc";
        "ndlr";
        "msbs";
        "mrbm";
        "http";
        "html";
        "gprs";
        "brrr";
        "bcbg";
      ]

  let%test _ =
    IntuitiveStupide.decoder_mot
      [ 3; 2; 3; 2; 3; 2; 3; 2; 3; 2; 3; 2; 3; 2 ]
      dico_fr_stupide
    = [
        "toxicomanogene";
        "seropositivite";
        "recapitulative";
        "monocotyledone";
        "hypovitaminose";
        "hyperemotivite";
        "heterometabole";
        "desiderabilite";
      ]

  let%test _ =
    IntuitiveStupide.decoder_mot
      [ 2; 3; 2; 3; 2; 3; 2; 3; 2; 3; 2; 3; 2; 3; 2 ]
      dico_fr_stupide
    = [ "aluminosilicate"; "adiposogenitale" ]

  let%test _ = IntuitiveStupide.decoder_mot [ 4; 3; 2 ] dico_fr_stupide = []

  (* Tests de max_mots_code_identique *)
  let%test _ = IntuitiveStupide.max_mots_code_identique S.empty = 0
  let%test _ = IntuitiveStupide.max_mots_code_identique dico_fr_stupide = 1155

  (* Tests de prefixe *)
  let%test _ =
    List.sort String.compare
      (IntuitiveStupide.prefixe [ 2; 2; 2; 2 ] dico_fr_stupide)
    = [
        "aieul";
        "aieule";
        "aieuls";
        "aieux";
        "ayeaye";
        "ayyubides";
        "eoue";
        "ouaille";
        "ouailles";
        "ouais";
        "ouaouaron";
        "ouie";
        "yaourt";
        "yaourtiere";
        "yeye";
        "youyou";
        "yoyo";
      ]

  let%test _ =
    List.sort String.compare
      (IntuitiveStupide.prefixe [ 3; 3; 3; 3 ] dico_fr_stupide)
    = [
        "bcbg";
        "brrr";
        "chthonien";
        "chthonienne";
        "dvdrom";
        "gprs";
        "html";
        "http";
        "mrbm";
        "msbs";
        "ndlr";
        "ntsc";
        "pgcd";
        "ppcm";
        "pschent";
        "schlague";
        "schlamms";
        "schlass";
        "schlinguant";
        "schlingue";
        "schlinguer";
        "schlittage";
        "schlittant";
        "schlitte";
        "schlitter";
        "schlitteur";
        "schnaps";
        "schnauzer";
        "schnock";
        "schnoque";
        "schnorchel";
        "schnorkel";
        "schnouf";
        "schnouff";
        "schproum";
        "sgbd";
        "sgml";
        "slbm";
        "sprl";
        "ssbs";
        "tvhd";
      ]

  let%test _ =
    List.sort String.compare (IntuitiveStupide.prefixe [] S.empty) = []
end

module IntuitiveStupideAssoc = IntuitiveStupideS (ListAssoc)
module IntuitiveStupideArbre = IntuitiveStupideS (Arbre)
