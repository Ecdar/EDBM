# Ecdar DBM Library
EDBM is a DBM (Difference bounds matrix) library for Rust. It is designed for the verification engines of ECDAR (Environment for Compositional Design and Analysis of Real Time Systems). 

EDBM is based on the main features from [UDBM](https://github.com/UPPAALModelChecker/UDBM) with some key differences:
- Rust memory and thread safety guarantees
- Concurrent operations on DBMs and Federations by making the shared memory model optional
- Type state usage protocol to ensure that DBMs are valid (non-empty and closed/in canonical form) when necessary and disallowing unnecessary close operations.

## Using EDBM
[EDBM is available on crates.io](...). The recommended way to use it is to add a dependency to your `Cargo.toml`:
```toml
[dependencies]
edbm = "0.1.0"
```

### Performance Optimization
To improve the performance of debug builds using EDBM one may add the following to `Cargo.toml`.
```toml
# Enable optimizations for EDBM in debug mode, but not for our code:
[profile.dev.package.edbm]
opt-level = 3
```
Do not build EDBM with the `expensive_asserts` feature enabled unless it is necessary for debugging internal EDBM consistency errors, it has a huge performance impact.

## License
EDBM is a derivative work of [UDBM](https://github.com/UPPAALModelChecker/UDBM) from the [UPPAAL](https://uppaal.org/) organization. This requires the project to be GNU General Public License v3.0. Source code directly based on UDBM code is marked with comments.
