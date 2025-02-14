mkdir -p tmp/WEB-INF/classes
cp -r $1/bin/pack tmp/WEB-INF/classes/.
cp -r $1/lib tmp/WEB-INF/.
cp -r $1/src/webcontent/* tmp/.
jar cf $1.war -C tmp .
rm -rf tmp
