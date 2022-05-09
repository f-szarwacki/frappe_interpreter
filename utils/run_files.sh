#!/bin/bash
# NOTE : Quote it else use array to avoid problems #
FILES=$*
for f in $FILES
do
  echo $f
  ./main $f
  echo -e "-----------------\n"
done