prefix="./States/"
fileIn=$(ls *.tvm)
postfix=".v"
fileOut="$var${postfix}"

for var in $fileIn; do

/home/ivan/devel/ton/coq-tvm-model/src/Computing.20.04.2020/tvmFileTranslatorAll1.native $var > $var${postfix}

echo $var

done
