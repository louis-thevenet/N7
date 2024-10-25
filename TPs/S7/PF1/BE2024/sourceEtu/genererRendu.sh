#!/bin/sh -e

echo "Saisissez votre login ENSEEIHT :"
read login
mkdir $login
cp -p chaines.ml $login
cp -p chaines.mli $login
cp -p dico_fr.txt $login
cp -p encodage.ml $login
cp -p intuitive.ml $login
cp -p structureDonnees.ml $login
cp -p testStupide.ml $login
cp -p testT9.ml $login
cp -p dune $login
cp -p dune-workspace $login
cp -p dune-project $login
tar -cvf  $login.tar $login
rm -rf $login

