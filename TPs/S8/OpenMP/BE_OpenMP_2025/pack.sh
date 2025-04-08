/usr/bin/env bash
USER=ltt5092
make clean;
mkdir $USER
cp -r bfs_traversal board circular_pipeline library modulo_parallel_for $USER;
cd $USER; find . -not \( -name  "*.c" -or  -name "Makefile" -or -name "*.h" -or -type d \) | xargs rm; cd ..;
tar zcvf $USER.tgz $USER;
rm -rf $USER;
