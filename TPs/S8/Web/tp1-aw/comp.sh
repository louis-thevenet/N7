mkdir -p tmp/WEB-INF/classes
cp -r $1/bin/pack tmp/WEB-INF/classes/.
cp -r $1/lib tmp/WEB-INF/.
for f in `ls $1/src/webcontent`
do
	cp $1/src/webcontent/$f tmp/.
done
jar cf $1.war -C tmp .
rm -rf tmp
