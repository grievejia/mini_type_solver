use std::error::Error;

use lalrpop::process_src;

fn main() -> Result<(), Box<dyn Error>> {
    process_src()?;
    Ok(())
}
