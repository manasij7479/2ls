#!/bin/bash
make -j9
#!/bin/bash
for filename in `ls "$1"`
do
  echo $filename 
  gtimeout 800s time ./2ls/2ls $1/$filename > /dev/null
  echo
done
