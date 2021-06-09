#/bin/bash

for f in $(find . -type f -name '*.sby')
do
	DIR=$(dirname "$f")
	FILE=$(basename "$f")
	echo "cd-ing into $DIR"
	cd $DIR
	echo "Executing SBY file $FILE"
	sby -f $FILE
	RES=${FILE%%.*}
	cp $RES/status ../status_${RES}
	rm -rf $RES
	cd -
done

for f in $(find . -type f -name '*.ys')
do
	DIR=$(dirname "$f")
	FILE=$(basename "$f")
	echo "cd-in into $DIR"
	cd $DIR
	echo "Executing SBY file $FILE"
	RES=${FILE%%.*}
	yosys $FILE | tee yosys_${RES}
	cd -
done

