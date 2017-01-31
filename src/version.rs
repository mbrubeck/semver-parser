use pest::prelude::*;
use std::fmt;

impl_rdp! {
    grammar! {
        version = _{ num ~ ["."] ~ num ~ ["."] ~ num ~ pre? ~ build? }

        pre     = { ["-"] ~ ids }
        ids     = _{ id ~ (["."] ~ id)* }
        id      = { num | alnum }

        build   = { ["+"] ~ alnums }
        alnums  = _{ alnum ~ (["."] ~ alnum)* }

        num     = { ["0"] | ['1'..'9'] ~ ['0'..'9']* }
        alnum   = { (['A'..'Z'] | ['a'..'z'] | ['0'..'9'] | ["-"])* }
    }

    process! {
        compute(&self) -> Result<Version, ()> {
            (x: parse_num(), y: parse_num(), z: parse_num(), pre: parse_pre(), build: parse_build()) => {
                Ok(Version { major: x, minor: y, patch: z, pre: pre?, build: build? })
            }
        }
        parse_pre(&self) -> Result<Vec<Identifier>, ()> {
            (_: pre, ids: maybe_ids()) => if ids.is_empty() { Err(()) } else { Ok(ids) },
            () => Ok(vec![])
        }
        parse_build(&self) -> Result<Vec<Identifier>, ()> {
            (_: build, ids: maybe_alnums()) => if ids.is_empty() { Err(()) } else { Ok(ids) },
            () => Ok(vec![])
        }
        maybe_ids(&self) -> Vec<Identifier> {
            (_: id, first: parse_id(), mut rest: maybe_ids()) => {
                rest.insert(0, first);
                rest
            },
            () => vec![]
        }
        parse_id(&self) -> Identifier {
            (&n: num) => Identifier::Numeric(n.parse::<u64>().unwrap()),
            (&id: alnum) => Identifier::AlphaNumeric(id.to_owned()),
        }
        parse_num(&self) -> u64 {
            (&n: num) => n.parse::<u64>().unwrap(),
        }
        maybe_alnums(&self) -> Vec<Identifier> {
            (&first: alnum, mut rest: maybe_alnums()) => {
                rest.insert(0, Identifier::AlphaNumeric(first.to_owned()));
                rest
            },
            () => vec![]
        }
    }
}


#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Version {
    pub major: u64,
    pub minor: u64,
    pub patch: u64,
    pub pre: Vec<Identifier>,
    pub build: Vec<Identifier>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Identifier {
    /// An identifier that's solely numbers.
    Numeric(u64),
    /// An identifier with letters and numbers.
    AlphaNumeric(String),
}

pub fn parse(version: &str) -> Result<Version, String> {
    let mut parser = Rdp::new(StringInput::new(version.trim()));
    if !parser.version() {
        return Err(From::from("Version did not parse properly."))
    }
    if !parser.end() {
        return Err(format!("Version did not end properly: {:?}", parser.queue()))
    }
    if let Ok(version) = parser.compute() {
        return Ok(version)
    }
    Err(From::from("Version did not compute properly."))
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{}.{}.{}", self.major, self.minor, self.patch));
        if !self.pre.is_empty() {
            let strs: Vec<_> =
                self.pre.iter().map(ToString::to_string).collect();
            try!(write!(f, "-{}", strs.join(".")));
        }
        if !self.build.is_empty() {
            let strs: Vec<_> =
                self.build.iter().map(ToString::to_string).collect();
            try!(write!(f, "+{}", strs.join(".")));
        }
        Ok(())
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Identifier::Numeric(ref id) => id.fmt(f),
            Identifier::AlphaNumeric(ref id) => id.fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use version;
    use super::*;

    #[test]
    fn parse_empty() {
        let version = "";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), "empty string incorrectly considered a valid parse");
    }

    #[test]
    fn parse_blank() {
        let version = "  ";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), "blank string incorrectly considered a valid parse");
    }

    #[test]
    fn parse_no_minor_patch() {
        let version = "1";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), format!("'{}' incorrectly considered a valid parse", version));
    }

    #[test]
    fn parse_no_patch() {
        let version = "1.2";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), format!("'{}' incorrectly considered a valid parse", version));
    }

    #[test]
    fn parse_empty_pre() {
        let version = "1.2.3-";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), format!("'{}' incorrectly considered a valid parse", version));
    }

    #[test]
    fn parse_letters() {
        let version = "a.b.c";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), format!("'{}' incorrectly considered a valid parse", version));
    }

    #[test]
    fn parse_with_letters() {
        let version = "1.2.3 a.b.c";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), format!("'{}' incorrectly considered a valid parse", version));
    }

    #[test]
    fn parse_basic_version() {
        let version = "1.2.3";

        let parsed = version::parse(version).unwrap();

        assert_eq!(1, parsed.major);
        assert_eq!(2, parsed.minor);
        assert_eq!(3, parsed.patch);
    }

    #[test]
    fn parse_trims_input() {
        let version = "  1.2.3  ";

        let parsed = version::parse(version).unwrap();

        assert_eq!(1, parsed.major);
        assert_eq!(2, parsed.minor);
        assert_eq!(3, parsed.patch);
    }

    #[test]
    fn parse_no_major_leading_zeroes() {
        let version = "01.0.0";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), "01 incorrectly considered a valid major version");
    }

    #[test]
    fn parse_no_minor_leading_zeroes() {
        let version = "0.01.0";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), "01 incorrectly considered a valid minor version");
    }

    #[test]
    fn parse_no_patch_leading_zeroes() {
        let version = "0.0.01";

        let parsed = version::parse(version);

        assert!(parsed.is_err(), "01 incorrectly considered a valid patch version");
    }

    #[test]
    fn parse_basic_prerelease() {
        let version = "1.2.3-pre";

        let parsed = version::parse(version).unwrap();

        let expected_pre = vec![Identifier::AlphaNumeric(String::from("pre"))];
        assert_eq!(expected_pre, parsed.pre);
    }

    #[test]
    fn parse_prerelease_alphanumeric() {
        let version = "1.2.3-alpha1";

        let parsed = version::parse(version).unwrap();

        let expected_pre = vec![Identifier::AlphaNumeric(String::from("alpha1"))];
        assert_eq!(expected_pre, parsed.pre);
    }

    #[test]
    fn parse_prerelease_zero() {
        let version = "1.2.3-pre.0";

        let parsed = version::parse(version).unwrap();

        let expected_pre = vec![Identifier::AlphaNumeric(String::from("pre")),
                                Identifier::Numeric(0)];
        assert_eq!(expected_pre, parsed.pre);
    }

    #[test]
    fn parse_basic_build() {
        let version = "1.2.3+build";

        let parsed = version::parse(version).unwrap();

        let expected_build = vec![Identifier::AlphaNumeric(String::from("build"))];
        assert_eq!(expected_build, parsed.build);
    }

    #[test]
    fn parse_build_alphanumeric() {
        let version = "1.2.3+build5";

        let parsed = version::parse(version).unwrap();

        let expected_build = vec![Identifier::AlphaNumeric(String::from("build5"))];
        assert_eq!(expected_build, parsed.build);
    }

    #[test]
    fn parse_pre_and_build() {
        let version = "1.2.3-alpha1+build5";

        let parsed = version::parse(version).unwrap();

        let expected_pre = vec![Identifier::AlphaNumeric(String::from("alpha1"))];
        assert_eq!(expected_pre, parsed.pre);

        let expected_build = vec![Identifier::AlphaNumeric(String::from("build5"))];
        assert_eq!(expected_build, parsed.build);
    }

    #[test]
    fn parse_complex_metadata_01() {
        let version = "1.2.3-1.alpha1.9+build5.7.3aedf  ";

        let parsed = version::parse(version).unwrap();

        let expected_pre = vec![Identifier::Numeric(1),
                                Identifier::AlphaNumeric(String::from("alpha1")),
                                Identifier::Numeric(9)];
        assert_eq!(expected_pre, parsed.pre);

        let expected_build = vec![Identifier::AlphaNumeric(String::from("build5")),
                                  Identifier::Numeric(7),
                                  Identifier::AlphaNumeric(String::from("3aedf"))];
        assert_eq!(expected_build, parsed.build);
    }

    #[test]
    fn parse_complex_metadata_02() {
        let version = "0.4.0-beta.1+0851523";

        let parsed = version::parse(version).unwrap();

        let expected_pre = vec![Identifier::AlphaNumeric(String::from("beta")),
                                Identifier::Numeric(1)];
        assert_eq!(expected_pre, parsed.pre);

        let expected_build = vec![Identifier::AlphaNumeric(String::from("0851523"))];
        assert_eq!(expected_build, parsed.build);
    }

    #[test]
    fn parse_regression_01() {
        let version = "0.0.0-WIP";

        let parsed = version::parse(version).unwrap();

        assert_eq!(0, parsed.major);
        assert_eq!(0, parsed.minor);
        assert_eq!(0, parsed.patch);

        let expected_pre = vec![Identifier::AlphaNumeric(String::from("WIP"))];
        assert_eq!(expected_pre, parsed.pre);
    }
}
