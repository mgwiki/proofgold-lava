GET https://formalweb3.uibk.ac.at/pgbce/bountiesall.php > b
cat b | grep ", C," | cut -d ',' -f 1 | sort | uniq -c | sort -n | tac | sed "s/^ *//" | while read c n; do echo "{\"name\":\"$n\", \"size\": $c},"; done
