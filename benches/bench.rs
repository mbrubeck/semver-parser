#![feature(test)]

extern crate semver_parser;
extern crate test;

use semver_parser::{version, range};

#[bench]
fn parse_version(b: &mut test::Bencher) {
    b.iter(move || {
        test::black_box(version::parse("123.456.789-alpha.1-pre.2"))
    });
}

#[bench]
fn parse_range(b: &mut test::Bencher) {
    b.iter(move || {
        test::black_box(range::parse("^0.1, =123.456.001, 5-6"))
    });
}
