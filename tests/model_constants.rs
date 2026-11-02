// The Rocq proofs that the constants of `Interval` from `E` to `TAU` are the tightest intervals
// around their values take their bounds from `rocq/theories/Model.v`, which gives each
// constant by the bit patterns of the floats that its two decimal literals round to, below a
// comment that gives those literals. This checks that the definitions of `Model.v` in that
// form are those of the constants below, each once, that their bit patterns are those of the
// bounds of the Rust constants, and that the decimals in the comment above each round to
// nearest to them.

use inari::Interval;
use std::{fs, path::Path};

// Each constant with its name, which `stringify!` gives, so that the two cannot disagree.
macro_rules! constants {
    ($($c:ident),*) => {
        [$((stringify!($c), Interval::$c)),*]
    };
}

const CONSTANTS: [(&str, Interval); 19] = constants!(
    E,
    FRAC_1_PI,
    FRAC_1_SQRT_2,
    FRAC_2_PI,
    FRAC_2_SQRT_PI,
    FRAC_PI_2,
    FRAC_PI_3,
    FRAC_PI_4,
    FRAC_PI_6,
    FRAC_PI_8,
    LN_10,
    LN_2,
    LOG10_2,
    LOG10_E,
    LOG2_10,
    LOG2_E,
    PI,
    SQRT_2,
    TAU
);

const FORM: &str = "rocq/theories/Model.v has to give each constant `C` as \
`Definition C : Interval :=` at the start of a line, with \
`  const_interval (from_bits 0x...) (from_bits 0x...).` on the next line, right below a \
comment `(** [pub const C: Self = const_interval!(a, b)] *)`, on one line or more, where `a` \
and `b` are the decimal literals of the bounds of the Rust constant.";

// A constant as `Model.v` gives it.
struct ModelConstant<'a> {
    name: &'a str,
    // The number of the line of its definition.
    line: usize,
    // The bit patterns of its bounds, from the line after the definition.
    bits: [u64; 2],
    // The decimal literals of its bounds, from the comment above the definition.
    decimals: [String; 2],
}

// Reads the constants of `Model.v` in the form that `FORM` gives. A line
// `Definition C : Interval :=` whose next line mentions `from_bits` has to be in that form, with
// its comment, or this panics. One whose next line does not, such as that of `ENTIRE`, is left
// out, and so is a definition that does not begin with such a line, such as one on one line.
// The test then fails if `C` is one of `CONSTANTS`, as the list lacks its name, but a constant
// that is not one of them goes unchecked.
fn read_constants(model: &str) -> Vec<ModelConstant<'_>> {
    let lines: Vec<&str> = model.lines().collect();
    let mut constants = vec![];
    for (i, line) in lines.iter().enumerate() {
        let Some(name) = line
            .strip_prefix("Definition ")
            .and_then(|s| s.strip_suffix(" : Interval :="))
        else {
            continue;
        };
        let next = lines.get(i + 1).copied().unwrap_or("");
        if !next.contains("from_bits") {
            continue;
        }
        let bits = read_definition(next).unwrap_or_else(|| {
            panic!(
                "Model.v:{}: cannot read the bit patterns of `{}`. {}",
                i + 2,
                name,
                FORM
            )
        });
        let decimals = read_comment(&lines[..i], name).unwrap_or_else(|| {
            panic!(
                "Model.v:{}: cannot read the comment above the definition of `{}`, or it names \
                 another constant. {}",
                i + 1,
                name,
                FORM
            )
        });
        constants.push(ModelConstant {
            name,
            line: i + 1,
            bits,
            decimals,
        });
    }
    constants
}

// Reads `const_interval (from_bits 0x...) (from_bits 0x...).`. The hex digits are read by
// value, so either case will do.
fn read_definition(line: &str) -> Option<[u64; 2]> {
    let rest = line
        .trim_start()
        .strip_prefix("const_interval (from_bits 0x")?
        .strip_suffix(").")?;
    let (a, b) = rest.split_once(") (from_bits 0x")?;
    Some([
        u64::from_str_radix(a, 16).ok()?,
        u64::from_str_radix(b, 16).ok()?,
    ])
}

// Reads the two decimals of `(** [pub const C: Self = const_interval!(a, b)] *)`, where `C` is
// `name`, from the comment that ends on the last of `above` and begins on the nearest line
// above it that begins with `(**`. Its lines are joined with every run of white space made one
// space, so that the comment may be wrapped at any of its spaces.
fn read_comment(above: &[&str], name: &str) -> Option<[String; 2]> {
    let end = above.len().checked_sub(1)?;
    if !above[end].trim_end().ends_with("*)") {
        return None;
    }
    let start = (0..=end)
        .rev()
        .find(|&j| above[j].trim_start().starts_with("(**"))?;
    let text = above[start..=end]
        .iter()
        .flat_map(|line| line.split_whitespace())
        .collect::<Vec<_>>()
        .join(" ");
    let rest = text
        .strip_prefix("(** [pub const ")?
        .strip_suffix(")] *)")?;
    let (c, rest) = rest.split_once(": Self = const_interval!(")?;
    if c != name {
        return None;
    }
    let (a, b) = rest.split_once(", ")?;
    Some([a.to_string(), b.to_string()])
}

// `Path::exists` would also return false if it cannot tell, and so skip where the test should
// fail.
fn exists(path: &Path) -> bool {
    path.try_exists()
        .unwrap_or_else(|e| panic!("cannot tell whether {} exists: {}", path.display(), e))
}

// CI runs wasmtime without `--dir`, so the test can read no file there, and would skip as for a
// published crate. It is ignored instead, so that the output shows it.
#[test]
#[cfg_attr(
    target_os = "wasi",
    ignore = "the test cannot read files under wasmtime without `--dir`"
)]
fn model_constants() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    // `cargo package` leaves `rocq/` out of the package (`include` in Cargo.toml), so the test of
    // a published crate has no `Model.v` to read, and skips. With `.git`, as in a clone of the
    // repository and in CI, it fails without `rocq/` instead, so that a missing `rocq/` cannot
    // pass unchecked. A Git repository made from the published crate fails too.
    if !exists(&root.join("rocq")) && !exists(&root.join(".git")) {
        eprintln!(
            "model_constants: skipped, as {} has neither rocq/ nor .git.",
            root.display()
        );
        return;
    }
    let path = root.join("rocq/theories/Model.v");
    let model = fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("cannot read {}: {}", path.display(), e));
    let found = read_constants(&model);

    let mut names: Vec<&str> = found.iter().map(|c| c.name).collect();
    names.sort_unstable();
    let mut expected: Vec<&str> = CONSTANTS.iter().map(|&(name, _)| name).collect();
    expected.sort_unstable();
    assert_eq!(
        names, expected,
        "Model.v gives other constants (left) than the test (right). {}",
        FORM
    );

    // The messages give bit patterns in hex, as `Model.v` does.
    for c in &found {
        let &(_, x) = CONSTANTS.iter().find(|&&(name, _)| name == c.name).unwrap();
        let rust = [x.inf().to_bits(), x.sup().to_bits()];
        assert!(
            c.bits == rust,
            "Model.v:{}: the bit patterns of the bounds of `{}`, {:#018x} and {:#018x}, differ \
             from those of `Interval::{}`, {:#018x} and {:#018x}.",
            c.line,
            c.name,
            c.bits[0],
            c.bits[1],
            c.name,
            rust[0],
            rust[1]
        );
        for (decimal, bits) in c.decimals.iter().zip(c.bits) {
            let parsed = decimal.parse::<f64>().unwrap_or_else(|e| {
                panic!(
                    "Model.v:{}: cannot read `{}` in the comment above `{}`: {}.",
                    c.line, decimal, c.name, e
                )
            });
            assert!(
                parsed.to_bits() == bits,
                "Model.v:{}: `{}` in the comment above `{}` rounds to nearest to {:#018x}, not \
                 to {:#018x}, the bit pattern in its definition.",
                c.line,
                decimal,
                c.name,
                parsed.to_bits(),
                bits
            );
        }
    }
    eprintln!(
        "model_constants: checked {} constants in {}.",
        found.len(),
        path.display()
    );
}
