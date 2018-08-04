#!/bin/bash

echo -n "gforth-fast  " >> log
echo -n $(git rev-parse HEAD) " " >> log
x=`nice -n -20 gforth-fast run.fth`
echo $x
echo $x >> log
