use anyhow::Result;
use std::path::PathBuf;
use structopt::StructOpt;
use vchain_plus::utils::KeyPair;

#[derive(StructOpt, Debug)]
struct Opt {
    /// Set Q
    #[structopt(short, long)]
    q: u64,

    /// Output path
    #[structopt(short, long, parse(from_os_str))]
    output: PathBuf,
}

fn main() -> Result<()> {
    let opt = Opt::from_args();
    let path = opt.output;
    let q = opt.q;
    let rng = rand::thread_rng();
    let key_pair = KeyPair::gen(q, rng);
    key_pair.save(path)?;
    Ok(())
}
