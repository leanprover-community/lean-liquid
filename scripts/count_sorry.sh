 #!/usr/bin/env bash

rg --count-matches sorry src | awk -F ':' 'BEGIN {sum = 0} {sum += $2} {print $2 " " $1} END {print sum " total"}'
