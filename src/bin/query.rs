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
    let res_path = opts.result;
    let pk = KeyPair::load_pk(&opts.pk_path)?;
    let mut query_info = Vec::new();
    for (i, q) in query_params.into_iter().enumerate() {
        info!("Processing query {}...", i);
        let (results, time) = query(&chain, q, &pk)?;
        info!("Total query time elapsed: {:?}", time);

        info!("Processing verification for query {}...", i);
        let verify_info = verify(&chain, results, &pk)?;
        info!(
            "Total verification time elapsed: {:?}",
            verify_info.verify_time
        );
        let res = json!({
            "query_time": time,
            "verify_info": verify_info,
        });
        query_info.push(res);
    }
    let s = serde_json::to_string_pretty(&query_info)?;
    fs::write(&res_path, &s)?;
    Ok(())
}
