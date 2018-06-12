#!/bin/bash
for filename in `ls "$1"`
do
  echo "timeout 800s time -f "%e" $2 $1/$filename 2>&1 | tail -n 3 | xargs | awk '{print \$1 \"\t\" \$NF}'"
done
