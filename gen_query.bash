#!/bin.bash
mkdir -p ./data/query/generated_query

# printf "generating range queries"
# cargo run --release --bin gen_query -- -r -t 10 -d 1 -s 0.0001 -g 500 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/range_t10_s0001
# cargo run --release --bin gen_query -- -r -t 50 -d 1 -s 0.001 -g 1000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/range_t50_s001
# cargo run --release --bin gen_query -- -r -t 100 -d 1 -s 0.01 -g 1000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/range_t100_s01
# cargo run --release --bin gen_query -- -r -t 500 -d 1 -s 0.05 -g 2000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/range_t500_s05
# cargo run --release --bin gen_query -- -r -t 1000 -d 1 -s 0.1 -g 4000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/range_t1000_s1

printf "generating keyword queries"
cargo run --release --bin gen_query -- -k -f -t 10 -n 1 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t10_n1
cargo run --release --bin gen_query -- -k -f -t 10 -n 2 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t10_n2
cargo run --release --bin gen_query -- -k -f -t 10 -n 4 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t10_n4
cargo run --release --bin gen_query -- -k -f -t 50 -n 1 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t50_n1
cargo run --release --bin gen_query -- -k -f -t 50 -n 2 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t50_n2
cargo run --release --bin gen_query -- -k -f -t 50 -n 4 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t50_n4
cargo run --release --bin gen_query -- -k -f -t 100 -n 1 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t100_n1
cargo run --release --bin gen_query -- -k -f -t 100 -n 2 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t100_n2
cargo run --release --bin gen_query -- -k -f -t 100 -n 4 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t100_n4
cargo run --release --bin gen_query -- -k -f -t 500 -n 1 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t500_n1
cargo run --release --bin gen_query -- -k -f -t 500 -n 2 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t500_n2
cargo run --release --bin gen_query -- -k -f -t 500 -n 4 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t500_n4
cargo run --release --bin gen_query -- -k -f -t 1000 -n 1 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t1000_n1
cargo run --release --bin gen_query -- -k -f -t 1000 -n 2 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t1000_n2
cargo run --release --bin gen_query -- -k -f -t 1000 -n 4 -s 0.1 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/keyword_t1000_n4

printf "generating keyword range queries"
#cargo run --release --bin gen_query -- -b -f -t 10 -d 1 -s 0.0001 -n 1 -g 500 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t10_n1
#cargo run --release --bin gen_query -- -b -f -t 10 -d 1 -s 0.0001 -n 2 -g 500 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t10_n2
#cargo run --release --bin gen_query -- -b -f -t 10 -d 1 -s 0.0001 -n 4 -g 500 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t10_n4
cargo run --release --bin gen_query -- -b -f -t 50 -d 1 -s 0.001 -n 1 -g 1000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t50_n1
cargo run --release --bin gen_query -- -b -f -t 50 -d 1 -s 0.001 -n 2 -g 1000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t50_n2
cargo run --release --bin gen_query -- -b -f -t 50 -d 1 -s 0.001 -n 4 -g 1000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t50_n4
cargo run --release --bin gen_query -- -b -f -t 100 -d 1 -s 0.01 -n 1 -g 1000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t100_n1
cargo run --release --bin gen_query -- -b -f -t 100 -d 1 -s 0.01 -n 2 -g 1000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t100_n2
cargo run --release --bin gen_query -- -b -f -t 100 -d 1 -s 0.01 -n 4 -g 1000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t100_n4
cargo run --release --bin gen_query -- -b -f -t 500 -d 1 -s 0.05 -n 1 -g 2000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t500_n1
cargo run --release --bin gen_query -- -b -f -t 500 -d 1 -s 0.05 -n 2 -g 2000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t500_n2
cargo run --release --bin gen_query -- -b -f -t 500 -d 1 -s 0.05 -n 4 -g 2000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t500_n4
cargo run --release --bin gen_query -- -b -f -t 1000 -d 1 -s 0.1 -n 1 -g 4000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t1000_n1
cargo run --release --bin gen_query -- -b -f -t 1000 -d 1 -s 0.1 -n 2 -g 4000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t1000_n2
cargo run --release --bin gen_query -- -b -f -t 1000 -d 1 -s 0.1 -n 4 -g 4000 -i ./data/db/eth_small_254/t2_id2_b4 -o ./data/query/generated_query/both_t1000_n4

