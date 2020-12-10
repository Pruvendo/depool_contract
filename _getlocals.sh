#!/bin/sh
grep -oh "LocalState_.*" src/LocalStateInstances.v | awk '{print $1}' | sed -e 's/[),.!&]//g' | sort | uniq
