//! Test utilities.

use crate::Function;

pub struct TestFunction {}

impl Function for TestFunction {
    fn len_values(&self) -> usize {
        todo!()
    }

    fn remat_cost(&self, val: crate::Val) -> Option<crate::RematCost> {
        todo!()
    }
}
