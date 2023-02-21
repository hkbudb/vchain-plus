# vChain+

**WARNING**: This is an academic proof-of-concept prototype, and in particular has not received careful code review. This implementation is NOT ready for production use.

If you find the code here useful, please consider to cite the following papers:

```bibtex
@inproceedings{ICDE22:vchain-plus,
  author = {Wang, Haixin and Xu, Cheng and Zhang, Ce and Xu, Jianliang and Peng, Zhe and Pei, Jian},
  title = {{vChain+}: Optimizing Verifiable Blockchain Boolean Range Queries},
  booktitle = {Proceedings of the 38th IEEE International Conference on Data Engineering},
  year = {2022},
  month = may,
  address = {Kuala Lumpur, Malaysia},
  pages = {1928--1941},
  issn = {2375-026X},
  doi = {10.1109/ICDE53745.2022.00190}
}
```
## Build

* Install Rust from <https://rustup.rs>.
* Run `cargo test` for unit test.
* Run `cargo build --release` to build the binaries, which will be located at `target/release/` folder.

## Generate public key

Run `gen_key` to generate the public key. You need to specify the universe size q. For example:

```
./target/release/gen_key -q 4096 -o /path/to/output_key
```
Run `./target/release/gen_key --help` for more info.

## Create Blockchain DB

#### Input Dataset Format

The input is a text file with each line represent an object.

```
obj := block_id [ v_data ] { w_data }
v_data := v_1, v_2, ...
w_data := w_1, w_2, ...
```

For 1-dimensional example

```
1 [1] {a,b,c}
1 [6] {a}
2 [4] {a,e}
```

For 2-dimensional example

```
1 [1,2] {a,b,c}
1 [1,5] {a}
2 [3,4] {a,e}
```
#### Build Blockchain
Run `build_chain` to build blockchain. You need to specify the sliding window size(s), the fan-out of ObjReg index and SWA-B+-Tree, the MaxID, and the numerical value dimension. Due to implementation design, please note that:
* the sliding window sizes should be defined in an ascending order;
* the suggested fan-out is 4;
* the MaxID should be at most q-1, where q is the universe size for public key generation.

For example:

```
./target/release/build_chain -t 2 -t 4 -t 8 -t 16 -t 32 --id-fanout 4 -b 4 -m 4095 -d 1 -k /path/to/pk -i /path/to/dataset.dat -r /path/to/res/build_time.json -o /path/to/output/db
```
Run `./target/release/build_chain --help` for more info.

## Query Processing & Verification

Encode query parameter as a JSON object. The following example specifies the query json file containing a query with the time window as [1, 50] and range as [10, 20], [5, 15] for 2 dimensional objects, and bool expression as "a" AND "b".

```json
  [
    {
      "start_blk": 1,
      "end_blk": 50,
      "range": [
        [
          10,
          20
        ],
        [
          5,
          15
        ]
      ],
      "keyword_exp": {
        "and": [
          {
            "input": "'a'"
          },
          {
            "input": "'b'"
          }
        ]
      }
    }
  ]
```

Run `query` to process queries & verify results. You need to specify the optimization(s) applied. Specifically:
* `-e`: enable optimizing query plan;
* `-n`: enable pruning empty sets.

In our implementation, query processing uses all available CPU cores while result verification uses only 4 threads as default to simulate a lightweight user. You can set the thread number for verification by setting the `-v` option. For example:

```
./target/release/query -e -n -k /path/to/pk -i /path/to/db -q /path/to/query.json -r /path/to/result/process_time.json -v 2
```
Run `./target/release/query --help` for more info.

