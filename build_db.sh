#!/bin.bash
DB_DIR='eth_small_254'
mkdir -p ./data/db/${DB_DIR}
mkdir -p ./data/result/${DB_DIR}
ID_FANOUT=2

echo "building db with t_w: 4, id_fanout: ${ID_FANOUT}, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 --id-fanout ${ID_FANOUT} -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t2_id${ID_FANOUT}_b4_build_res.json -o ./data/db/${DB_DIR}/t2_id${ID_FANOUT}_b4

echo "building db with t_w: 8, id_fanout: ${ID_FANOUT}, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 --id-fanout ${ID_FANOUT} -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t3_id${ID_FANOUT}_b4_build_res.json -o ./data/db/${DB_DIR}/t3_id${ID_FANOUT}_b4

echo "building db with t_w: 16, id_fanout: ${ID_FANOUT}, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 --id-fanout ${ID_FANOUT} -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t4_id${ID_FANOUT}_b4_build_res.json -o ./data/db/${DB_DIR}/t4_id${ID_FANOUT}_b4

echo "building db with t_w: 32, id_fanout: ${ID_FANOUT}, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 -t 32 --id-fanout ${ID_FANOUT} -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t5_id${ID_FANOUT}_b4_build_res.json -o ./data/db/${DB_DIR}/t5_id${ID_FANOUT}_b4

