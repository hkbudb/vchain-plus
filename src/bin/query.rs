#[macro_use]
extern crate tracing;

use anyhow::Result;
use serde_json::json;
use std::{fs, path::PathBuf};
use structopt::StructOpt;
use vchain_plus::{
    chain::{query::query, verify::verify},
    utils::{init_tracing_subscriber, load_query_param_from_file, KeyPair},
    SimChain,
};

#[derive(StructOpt, Debug)]
struct Opt {
    // empty set process
    #[structopt(short, long)]
    null_set: bool,

    // egg optimize
    #[structopt(short, long)]
    egg_opt: bool,

    /// verification thread number
    #[structopt(short, long, default_value = "4")]
    verify_thread_num: usize,

    /// pk path
    #[structopt(short, long, parse(from_os_str))]
    key_path: PathBuf,

    /// input db path, should be a directory
    #[structopt(short, long, parse(from_os_str))]
    input: PathBuf,

    /// query path, should be a file
    #[structopt(short, long, parse(from_os_str))]
    query: PathBuf,

    /// result path, should be a file
    #[structopt(short, long, parse(from_os_str))]
    result: PathBuf,
}

fn main() -> Result<()> {
    init_tracing_subscriber("query=info,vchain_plus::chain=off")?;
    //init_tracing_subscriber("info")?;
    let opts = Opt::from_args();
    let verify_thread_num = opts.verify_thread_num;
    let query_path = opts.query;
    let query_params = load_query_param_from_file(&query_path)?;
    let db_path = opts.input;
    let chain = SimChain::open(&db_path)?;
    let res_path = opts.result;
    let pk = KeyPair::load(&opts.key_path)?.pk;
    let mut query_info = Vec::new();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(verify_thread_num)
        .build()?;
    for (i, q) in query_params.into_iter().enumerate() {
        info!("Processing query {}...", i);
        let (results, res_dags, time) = query(opts.null_set, opts.egg_opt, &chain, q, &pk)?;
        info!("Query time elapsed: {:?}", time);

        info!("Verifying query {}...", i);
        let verify_info = pool.install(|| verify(&chain, &results, &res_dags, &pk))?;
        info!("Verification time elapsed: {:?}", verify_info.verify_time);
        let res = json!({
            "query_info": time,
            "verify_info": verify_info,
        });
        query_info.push(res);
        info!("=================");
    }
    let s = serde_json::to_string_pretty(&query_info)?;
    fs::write(&res_path, &s)?;
    Ok(())
}
