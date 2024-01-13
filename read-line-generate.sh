#!/bin/sh

cat -v read-line.txt | sed 's/"/\\"/g'| sed 's/^/printf("/' | sed 's/$/\\n/' | sed 's/$/");/' > read-line-coded.txt

#EOF