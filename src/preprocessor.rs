use std::{fs::OpenOptions, io::Read, path::PathBuf};

const INCLUDE_STR: &str = "#include ";

fn process_include_line(working_dir: PathBuf, line: String) -> String {
    let mut fpath: PathBuf = line.into();

    fpath = if fpath.is_relative() {
        let mut new_fpath: PathBuf = working_dir.clone().into();
        new_fpath.push(&fpath);

        new_fpath
    } else {
        fpath
    };

    let mut f = match OpenOptions::new().read(true).open(fpath) {
        Ok(v) => v,
        Err(_) => {
            return "".to_owned();
        }
    };

    let mut contents = String::new();

    if let Err(_) = f.read_to_string(&mut contents) {
        return "".to_owned();
    }

    contents
}

/// Replaces #include statements with the specified file
pub fn parser(working_dir: PathBuf, input: &str) -> String {
    input
        .lines()
        .map(|line| {
            let mut contents = if line.starts_with(INCLUDE_STR) {
                line.split(INCLUDE_STR)
                    .nth(1)
                    .map(|fname| process_include_line(working_dir.clone(), fname.to_owned()))
                    .unwrap_or(line.to_owned())
            } else {
                line.to_owned()
            };

            contents.push_str("\n");

            contents
        })
        .collect::<String>()
}
