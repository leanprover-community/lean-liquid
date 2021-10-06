#!/bin/bash

git grep -l sorry | grep -v scripts | xargs -I % sh -c 'nsorry=`grep sorry % | wc -l`; echo -n "$nsorry\t%\n"'; echo -en "Total:\t"; git grep sorry | grep -v scripts | wc -l
