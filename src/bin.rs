use edbm::util::constraints::Inequality;

use Inequality::*;

use edbm::zones::{OwnedFederation, DBM};

fn main() {
    const DIM: usize = 10;
    let fed1 = OwnedFederation::init(DIM);
    let dbm = DBM::init(DIM)
        .constrain_and_close(1, 0, LE(5)) // Lower bound
        .unwrap()
        .constrain_and_close(0, 1, LE(-5)) // Upper bound
        .unwrap();

    let fed2 = OwnedFederation::from_dbms(vec![dbm]);

    let res = fed1.clone().subtract(&fed2);

    let init_minus_res = fed1.clone().subtract(&res);

    println!("res: {res}");
    println!("init_minus_res: {init_minus_res}");

    assert!(res.equals(&res));
    assert!(init_minus_res.equals(&init_minus_res));

    let fed_sum = res.append(&init_minus_res);
    println!("fed_sum: {fed_sum}");

    assert!(fed_sum.equals(&fed1));
}
