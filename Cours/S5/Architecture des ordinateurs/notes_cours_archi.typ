#import "../../templates/template.typ": *
#import "@preview/physica:0.8.0": * // for dd()

#show: project.with(
  title: "Architecture - Notes de cours",
  authors: ("THEVENET Louis",),
  date: "November 16, 2023",
)

= Minimisation des fonctions booléennes
$ mat(
  space, 00, 01, 11, 10, arrow.dotted a overline(c);00, 1, space, space, 1, arrow.dotted a b d;01, space, space, 1, space, arrow.dotted b c d;11,
    1,
    1,
    1,
    space,
    arrow.dotted overline(a) overline(b) space.hair overline(d);10,
    1,
    1,
    space,
    space,
    arrow.dotted overline(b) overline(c) overline(d),
,
) $

$ f(a,b,c,d) = a overline(c) + b c d + overline(a) overline(b) overline(d)$