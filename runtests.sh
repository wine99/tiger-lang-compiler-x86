#!/bin/sh 
_build/install/default/bin/runtests "$@" 2>&1
exit $?