#/bin/bash 

RESTEASY_HOME=/home/hagimont/install/resteasy-jaxrs-3.0.9.Final
cd students-client/bin

java -cp .:$RESTEASY_HOME/lib/* TestClient

cd ../..
