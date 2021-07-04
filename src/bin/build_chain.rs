#[macro_use]
extern crate tracing;

use anyhow::Result;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use structopt::StructOpt;
use vchain_plus::utils::{init_tracing_subscriber, KeyPair};
use vchain_plus::{
    chain::{
        block::{build::build_block, Height},
        object::Object,
        traits::WriteInterface,
        Parameter,
    },
    digest::{Digest, Digestible},
    utils::{load_raw_obj_from_file, Time},
    SimChain,
};

#[derive(StructOpt, Debug)]
struct Opt {
    /// time windows
    #[structopt(short = "-t", long)]
    time_win_sizes: Vec<u64>,

    /// id tree fanout
    #[structopt(short = "-f", long)]
    id_fanout: usize,

    /// max id num
    #[structopt(short = "-m", long)]
    max_id: usize,

    /// bplus tree fanout
    #[structopt(short = "-b", long)]
    bplus_fanout: usize,

    /// dimension
    #[structopt(short = "-d", long)]
    dim: usize,

    /// pk path
    #[structopt(short = "-p", long, parse(from_os_str))]
    pk_path: PathBuf,

    /// input path, should be a file
    #[structopt(short, long, parse(from_os_str))]
    input: PathBuf,

    /// result path, should be a file
    #[structopt(short, long, parse(from_os_str))]
    result: PathBuf,

    /// output path, should be a directory
    #[structopt(short, long, parse(from_os_str))]
    output: PathBuf,
}

#[derive(Debug, Serialize, Deserialize)]
struct BuildTime {
    blk_height: Height,
    build_time: Time,
}

fn build_chain(
    data_path: &Path,
    pk_path: &Path,
    db_path: &Path,
    res_path: &Path,
    param: &Parameter,
) -> Result<()> {
    if !db_path.exists() {
        fs::create_dir_all(db_path)?;
    }
    let mut chain = SimChain::create(db_path, param.clone())?;
    chain.set_parameter(param)?;
    let mut prev_hash = Digest::zero();
    let raw_objs: BTreeMap<Height, Vec<Object<u32>>> = load_raw_obj_from_file(data_path)?;
    let pk = KeyPair::load_pk(pk_path)?;
    let mut time_set = Vec::<BuildTime>::new();
    let timer = howlong::ProcessCPUTimer::new();
    for (blk_height, objs) in raw_objs {
        let (blk_head, duration) =
            build_block(blk_height, prev_hash, objs, &mut chain, &param, &pk)?;
        prev_hash = blk_head.to_digest();
        time_set.push(BuildTime {
            blk_height,
            build_time: duration.into(),
        });
    }
    let time = timer.elapsed();
    info!("Block building finished. Time elapsed: {}", time);
    let res = json!({
        "total_time": Time::from(time),
        "time_set": time_set,
    });
    let s = serde_json::to_string_pretty(&res)?;
    fs::write(res_path, &s)?;
    Ok(())
}

fn main() -> Result<()> {
    init_tracing_subscriber("info")?;
    let opts = Opt::from_args();
    let param = Parameter {
        time_win_sizes: opts.time_win_sizes,
        id_tree_fanout: opts.id_fanout,
        max_id_num: opts.max_id,
        bplus_tree_fanout: opts.bplus_fanout,
        num_dim: opts.dim,
    };
    build_chain(
        &opts.input,
        &opts.pk_path,
        &opts.output,
        &opts.result,
        &param,
    )?;
    Ok(())
}
