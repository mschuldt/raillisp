#!/bin/bash

if [[ $EUID -ne 0 ]]; then
    echo "must be run as root"
    exit 1
fi

echo -n "3 gforth-fast  " >> log
echo -n $(git rev-parse HEAD) " " >> log
x=`nice -n -20 gforth-fast run.fth`
echo $x
echo $x >> log
