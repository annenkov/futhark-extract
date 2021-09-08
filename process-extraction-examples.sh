#!/bin/bash

FUTHARK_PATH=./extracted/auto-generated

rm $FUTHARK_PATH/*.fut -f

echo "Processing Futhark extraction"
for f in $FUTHARK_PATH/*.fut.out;
do
    echo $f "--->" $FUTHARK_PATH/$(basename ${f%.out}) ;
    cp ${f} $FUTHARK_PATH/$(basename ${f%.out})
done
