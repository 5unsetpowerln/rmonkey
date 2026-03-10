use anyhow::Error;

pub fn print_errors(msg: &str, err: Error) {
    println!("{msg}: {err}");

    let mut current = err.source();

    while let Some(s) = current {
        println!("\t<- {s}");
        current = s.source();
    }
}

pub fn push_u16_to_bytes_big_endian(vector: &mut Vec<u8>, value: u16) {
    let upper = (value >> 8) as u8;
    let lower = (value & 0xff) as u8;

    vector.push(upper);
    vector.push(lower);
}

pub fn concatenate_insts_list(insts_list: &[Vec<u8>]) -> Vec<u8> {
    let mut output_insts = Vec::new();

    for insts in insts_list.iter() {
        for inst in insts.iter() {
            output_insts.push(*inst);
        }
    }

    output_insts
}
