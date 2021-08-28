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
        printf "query: %s, db: %s\n" ${q} ${db}
        cargo run --release --bin query -- -k ./keys/keys_2048 -i data/db/${DB_DIR}/${db} -q ./data/query/generated_query/${q}/vchain_plus.json -r ./data/result/${DB_DIR}/${db}/${q}_query_res.json
    done
done
