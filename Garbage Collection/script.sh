# Help me write a script which copies each of ./testcases/Test1/Test.java into ./testcase and compares the output with ./testcase/Testi/Test with the output thrown from ./run.sh and store in output_i.txt

# script for copies each of Test.java into ./testcase 

# read folder names in ./testcases
for folder in ./testcases/*; do
    # read file names in each folder
    for file in $folder/*; do
        # copy Test.java into ./testcase
        cp $file ./testcase
        # get the file name without extension
        filename=$(basename -- "$file")
        filename="${filename%.*}"
        # run the script and store the output in output_i.txt
        ./run.sh > output_$filename.txt
        # compare the output with ./testcase/Testi/Test
        diff output_$filename.txt ./testcase/$filename/Test
    done
done