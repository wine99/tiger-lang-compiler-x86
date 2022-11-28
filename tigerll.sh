#!/bin/sh
LLOUTDIR=_build/ll/
mkdir -p $LLOUTDIR
FILE=`basename $1`
#TEMPFILE=`mktemp $LLOUTDIR$FILE.XXXXXXXX`
TEMPFILE=$LLOUTDIR$FILE
TEMPFILELL=$TEMPFILE.ll
# mv $TEMPFILE $TEMPFILELL
_build/install/default/bin/tigerc $1 -p llvm -o $TEMPFILELL
if [ $? -ne 0 ]; then 
  exit $?
fi
echo "LL file generated at $TEMPFILELL"  
clang src/compiler/llcodegen/runtime.c $TEMPFILELL -o $TEMPFILE.out
echo "Out file generated at $TEMPFILE.out"  