echo "n,conflicts,clauses,literals,,,progress,runtime,conflicts,clauses,literals,learned clauses,learned literals" > data.csv
for i in {10..180..10}
do
	echo -n $i,  >> data.csv
	./satTest $i | grep -oP '\d+\.?\d*' | tr '\n' ','  >> data.csv
	echo >> data.csv
	echo $i done
done
