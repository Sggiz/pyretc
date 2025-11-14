#!/bin/bash

option=$1

dune build $(pwd)/_build/default/pyretc.exe

case $option in
    "" )
        $(pwd)/_build/default/pyretc.exe $(pwd)/test/test.arr;;
    "--parse-only" )
        $(pwd)/_build/default/pyretc.exe --parse-only \
            $(pwd)/test/test.arr;;
    * )
        cd $(pwd)/jcftest
        sh script.sh $option ../_build/default/pyretc.exe;;
esac
echo

