# run javac on ./testcase folder 
./clean.sh
javac -g  ./testcase/*.java
javac -cp .:sootclasses-trunk-jar-with-dependencies.jar PA2.java
java -cp .:sootclasses-trunk-jar-with-dependencies.jar PA2


