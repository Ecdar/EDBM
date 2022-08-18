pub mod memory;
pub mod util;
pub mod zones;

#[macro_export]
#[cfg(feature = "expensive_asserts")]
macro_rules! expensive_assert {
    ($e:expr) => {
        assert!($e);
    };
}

#[macro_export]
#[cfg(not(feature = "expensive_asserts"))]
macro_rules! expensive_assert {
    ($e:expr) => {};
}
