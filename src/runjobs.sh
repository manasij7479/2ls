#!/bin/bash
for job in `ls "$1"`
do
  parallel -k < $1/$job > $1/$job-result.txt
done
