#!/bin.bash
DB_DIR='eth_small_254'
mkdir -p ./data/db/${DB_DIR}
mkdir -p ./data/result/${DB_DIR}

echo "building db with t_w: 4, id_fanout: 4, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 --id-fanout 4 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t4_id4_b4_build_res.json -o ./data/db/${DB_DIR}/t4_id4_b4
echo "building db with t_w: 4, id_fanout: 8, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 --id-fanout 8 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t4_id8_b4_build_res.json -o ./data/db/${DB_DIR}/t4_id8_b4
echo "building db with t_w: 4, id_fanout: 16, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 --id-fanout 16 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t4_id16_b4_build_res.json -o ./data/db/${DB_DIR}/t4_id16_b4
echo "building db with t_w: 4, id_fanout: 32, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 --id-fanout 32 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t4_id32_b4_build_res.json -o ./data/db/${DB_DIR}/t4_id32_b4
echo "building db with t_w: 8, id_fanout: 4, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 --id-fanout 4 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t8_id4_b4_build_res.json -o ./data/db/${DB_DIR}/t8_id4_b4
echo "building db with t_w: 8, id_fanout: 8, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 --id-fanout 8 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t8_id8_b4_build_res.json -o ./data/db/${DB_DIR}/t8_id8_b4
echo "building db with t_w: 8, id_fanout: 16, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 --id-fanout 16 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t8_id16_b4_build_res.json -o ./data/db/${DB_DIR}/t8_id16_b4
echo "building db with t_w: 8, id_fanout: 32, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 --id-fanout 32 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t8_id32_b4_build_res.json -o ./data/db/${DB_DIR}/t8_id32_b4
echo "building db with t_w: 16, id_fanout: 4, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 --id-fanout 4 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t16_id4_b4_build_res.json -o ./data/db/${DB_DIR}/t16_id4_b4
echo "building db with t_w: 16, id_fanout: 8, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 --id-fanout 8 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t16_id8_b4_build_res.json -o ./data/db/${DB_DIR}/t16_id8_b4
echo "building db with t_w: 16, id_fanout: 16, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 --id-fanout 16 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t16_id16_b4_build_res.json -o ./data/db/${DB_DIR}/t16_id16_b4
echo "building db with t_w: 16, id_fanout: 32, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 --id-fanout 32 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t16_id32_b4_build_res.json -o ./data/db/${DB_DIR}/t16_id32_b4
echo "building db with t_w: 32, id_fanout: 4, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 -t 32 --id-fanout 4 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t32_id4_b4_build_res.json -o ./data/db/${DB_DIR}/t32_id4_b4
echo "building db with t_w: 32, id_fanout: 8, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 -t 32 --id-fanout 8 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t32_id8_b4_build_res.json -o ./data/db/${DB_DIR}/t32_id8_b4
echo "building db with t_w: 32, id_fanout: 16, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 -t 32 --id-fanout 16 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t32_id16_b4_build_res.json -o ./data/db/${DB_DIR}/t32_id16_b4
echo "building db with t_w: 32, id_fanout: 32, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 -t 32 --id-fanout 32 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t32_id32_b4_build_res.json -o ./data/db/${DB_DIR}/t32_id32_b4
echo "building db with t_w: 64, id_fanout: 4, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 -t 32 -t 64 --id-fanout 4 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t64_id4_b4_build_res.json -o ./data/db/${DB_DIR}/t64_id4_b4
echo "building db with t_w: 64, id_fanout: 8, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 -t 32 -t 64 --id-fanout 8 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t64_id8_b4_build_res.json -o ./data/db/${DB_DIR}/t64_id8_b4
echo "building db with t_w: 64, id_fanout: 16, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 -t 32 -t 64 --id-fanout 16 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t64_id16_b4_build_res.json -o ./data/db/${DB_DIR}/t64_id16_b4
echo "building db with t_w: 64, id_fanout: 32, bplus_fanout: 4"
cargo run --release --bin build_chain -- -t 2 -t 4 -t 8 -t 16 -t 32 -t 64 --id-fanout 32 -m 4095 -b 4 -d 1 -k ./keys/254_4096 -i ./data/dataset/eth-small.dat -r ./data/result/${DB_DIR}/t64_id32_b4_build_res.json -o ./data/db/${DB_DIR}/t64_id32_b4
