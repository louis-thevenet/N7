#!/bin/sh -e

echo "Saisissez votre login ENSEEIHT :"
read login
mkdir $login
cp -p arbre.ml $login
cp -p base.ml $login
cp -p conversion.ml $login
cp -p liste.ml $login
cp -p natset.ml $login
cp -p dune $login
cp -p dune-workspace $login
cp -p dune-project $login
tar -cvf  $login.tar $login
rm -rf $login

