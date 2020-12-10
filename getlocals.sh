#!/bin/sh
grep -oh "LocalState_.*" src/DePoolFunc.v | awk '{print $1}' | sed -e 's/[),.!&]//g' | sort | uniq
