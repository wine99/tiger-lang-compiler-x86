#!/bin/sh
LLOUTDIR=_build/js/
mkdir -p $LLOUTDIR
FILE=`basename $1`
# TEMPFILE=`mktemp $LLOUTDIR$FILE.XXXXXXXX`
TEMPFILE=$LLOUTDIR$FILE
TEMPFILELL=$TEMPFILE.html
# mv $TEMPFILE $TEMPFILELL
_build/install/default/bin/tigerc $1 -p js -o $TEMPFILELL
if [ $? -ne 0 ]; then 
  exit $?
fi
echo "HTML file generated at $TEMPFILELL"  
