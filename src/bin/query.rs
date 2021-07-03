use anyhow::Result;
use serde_json::json;
use std::{fs, path::PathBuf};
use structopt::StructOpt;
use tracing::{debug, info};
use vchain_plus::{
    chain::{query::query, verify::verify},
    utils::{init_tracing_subscriber, load_query_param_from_file, KeyPair},
    SimChain,
};

#[derive(StructOpt, Debug)]
struct Opt {
    /// activate optimize mode
    #[structopt(short, long)]
    optimized: bool,

    /// pk path
    #[structopt(short = "-p", long, parse(from_os_str))]
    pk_path: PathBuf,

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
    init_tracing_subscriber("debug")?;
    let opts = Opt::from_args();
    let query_path = opts.query;
    let query_params = load_query_param_from_file(&query_path)?;
    let db_path = opts.input;
    let chain = SimChain::open(&db_path)?;
    let optimized = opts.optimized;
    let res_path = opts.result;
    let pk = KeyPair::load_pk(&opts.pk_path)?;
    let mut query_info = Vec::new();
    for (i, q) in query_params.into_iter().enumerate() {
        debug!("Processing query {}...", i);
        let timer = howlong::ProcessCPUTimer::new();
        let ((res, vo), time) = query(&chain, q, optimized, &pk)?;
        let total_time = timer.elapsed();
        info!(
            "Total time elapsed: {:?}, CPU usage: {:.2}",
            total_time,
            total_time.cpu_usage()
        );
        debug!("Processing verification for query {}...", i);
        let verify_info = verify(&chain, &res, vo, &pk)?;
        let res = json!({
            "total_time": total_time.to_string(),
            "query_time": time,
            "verify_info": verify_info,
        });
        query_info.push(res);
    }
    let s = serde_json::to_string_pretty(&query_info)?;
    fs::write(&res_path, &s)?;
    Ok(())
}
