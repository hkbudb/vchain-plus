#!/bin.bash
DB_DIR='eth_small_254'
DBS=`eval ls ./data/db/${DB_DIR}`
QS=`eval ls ./data/query/generated_query`

for db in ${DBS[*]}
do
    mkdir -p ./data/result/${DB_DIR}/${db}
done
for db in ${DBS[*]}
do
    for q in ${QS[*]}
    do
        printf "query: %s, db: %s\n using basic approach" ${q} ${db}
        cargo run --release --bin query -- -o 0 -k ./keys/254_4096 -i data/db/${DB_DIR}/${db} -q ./data/query/generated_query/${q}/vchain_plus.json -r ./data/result/${DB_DIR}/${db}/${q}_basic_query.json
        printf "query: %s, db: %s\n using trimmed approach" ${q} ${db}
        cargo run --release --bin query -- -o 2 -k ./keys/254_4096 -i data/db/${DB_DIR}/${db} -q ./data/query/generated_query/${q}/vchain_plus.json -r ./data/result/${DB_DIR}/${db}/${q}_trimmed_query.json
        printf "query: %s, db: %s\n using trimmed2 approach" ${q} ${db}
        cargo run --release --bin query -- -o 1 -k ./keys/254_4096 -i data/db/${DB_DIR}/${db} -q ./data/query/generated_query/${q}/vchain_plus.json -r ./data/result/${DB_DIR}/${db}/${q}_trimmed2.json
    done
done
