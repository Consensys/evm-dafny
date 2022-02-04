#! /bin/bash
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

error=0
processeddirs=0

mydirs=()
mydirsstatus=()

# help and usage
help()
{
   # Display Help
   echo "Usage: $0 dir, where dirname is the folder you want to check."
   echo "All .dfy files in the folder dirname will be checked."
   echo
}

# Check number of arguments
if  [ "$#" -ne 1 ];  
    then 
    echo "Illegal number of parameters"
    help
    exit 1
fi

if [ ! -d "$1" ] 
then
    echo -e "${RED}Error: Root directory $1 DOES NOT exists.${NC}" 
    exit 2 
fi

echo "Processing " $1
LOG_FILE=$1/verif-`date +'%Y-%m-%d-%H:%M:%S'`.log
./verifyAll.sh $1 | tee $LOG_FILE
if [ $? -eq 0 ] # check if errors
then
  echo -e "${GREEN}No errors in directory $dir${NC}"
else
  echo -e "${RED}Some errors occured in directory $dir${NC}"
  error=$((error + 1))
fi

# The list of dirs 
listofdirs=`find $1 -maxdepth 1 -mindepth 1 -type d`
# listofdirs=`find $1 -maxdepth 1 -mindepth 1 -type d -printf '%p\n'`
for dir in $listofdirs
do
    echo "Processing directories in " $dir
    mydirs+=($dir)
    ./verifyAllRec.sh $dir
    if [ $? -eq 0 ] # check if errors
    then
      echo -e "${GREEN}No errors in directory $dir${NC}"
      mydirsstatus+=(1)
    else
      echo -e "${RED}Some errors occured in directory $dir${NC}"
      error=$((error + 1))
      mydirsstatus+=(0)
    fi
done

if [ $error -ne 0 ]
then
  echo -e "${RED}Some directories [$error/$processeddirs] has(ve) errors :-("
  for i in ${!mydirs[@]}; do
  if [ ${mydirsstatus[$i]} -ne 1 ]
  then
    echo -e "${RED}[FAIL] ${mydirs[$i]} has some errors :-(${NC}"
  else 
     echo -e "${GREEN}[OK] ${mydirs[$i]}${NC}" 
  fi
done
  exit 1
else 
  echo -e "${GREEN}No errors in any dirs! Great job.${NC}"
  exit 0
fi

