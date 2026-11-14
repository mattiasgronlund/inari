// The run-time choice of the copy of the kernel's entries that uses an FMA.
//
// Under `cfg(inari_kernel_dispatch)`, which `build.rs` sets for x86-64 targets without `sse4.2`
// and without the feature `force-generic`, `HAS_FMA` is false, and each entry that
// `level_entry!` defines calls one of two copies of its body `<f>_with::<FMA>`: on a CPU that has
// `fma`, `fma_copy`, compiled with that target feature, in which `two_prod_err::<true>` is one
// FMA instruction; on any other, `dekker_copy`. Every function on the path from `<f>_with` to
// `two_prod_err` is `#[inline(always)]` under that `cfg`, so that `fma_copy` compiles it with the
// feature, but for five that stay `#[inline(never)]`: `fast_atan2_dir2` of `atan.rs`, and
// `fast_band`, `fast_band_big`, `fast_tan_band` and `fast_tan_band_big` of `trig.rs`. Compiled
// without the feature, their copies with `FMA` true compute `two_prod_err` with a call of the
// library's `fma`, which rounds as the instruction does. Both copies return the same `f64`s, as
// `FMA` only chooses how `two_prod_err` computes the error of a product, and the proofs in
// `rocq/` show that the fast paths return the same with either value of it (`fast_exp_dir_fma`
// in `rocq/theories/FastExp.v` and the others), and so does `exact_div`, which the rules of
// atan2 call (`exact_div_fma` in `rocq/theories/AtanExactDiv.v`).
//
// Every other build compiles each entry once, as `<f>_with::<HAS_FMA>`, and takes no decision at
// run time.

cfg_if::cfg_if! {
    if #[cfg(inari_kernel_dispatch)] {
        use std::sync::atomic::{AtomicU8, Ordering};

        // 0: not detected yet, 1: the CPU has no `fma`, 2: it has. Only `detect` stores, and it
        // stores 2 only after `is_x86_feature_detected!("fma")` has said yes.
        static LEVEL: AtomicU8 = AtomicU8::new(0);

        // The test on the FMA path of every entry: one compare of a byte in memory.
        #[inline(always)]
        pub(super) fn fma_ready() -> bool {
            LEVEL.load(Ordering::Relaxed) == 2
        }

        // Whether the CPU has `fma`, detected on the first call. The test on the entries' cold
        // path.
        #[inline(always)]
        pub(super) fn fma_detected() -> bool {
            match LEVEL.load(Ordering::Relaxed) {
                0 => detect(),
                level => level == 2,
            }
        }

        #[cold]
        #[inline(never)]
        fn detect() -> bool {
            // `--cfg inari_force_no_fma` in RUSTFLAGS answers "no" on any CPU, to test and count
            // the Dekker copies on a CPU that has `fma`.
            let yes = !cfg!(inari_force_no_fma) && std::is_x86_feature_detected!("fma");
            LEVEL.store(if yes { 2 } else { 1 }, Ordering::Relaxed);
            yes
        }
    }
}

// Defines an entry of the kernel, `$name`, from its body `$with<const FMA: bool>`, which must be
// `#[inline(always)]`. Three forms, by how the entry takes its direction:
//
//     level_entry! { fn sin_dir<const UP: bool>(x: f64) -> f64 = sin_dir_with; }
//     level_entry! { fn exp(x: f64, up: bool) -> f64 = exp_with; }
//     level_entry! { fn sin_near(x: f64) -> f64 = sin_near_with; }
//
// with `$with` declared as `fn sin_dir_with<const FMA: bool, const UP: bool>(x: f64) -> f64`,
// `fn exp_with<const FMA: bool>(x: f64, up: bool) -> f64` and
// `fn sin_near_with<const FMA: bool>(x: f64) -> f64`. Attributes, doc comments and a visibility
// before `fn` go to the entry. The macro adds no `inline` attribute of its own to the entry, so
// that a build without the dispatch keeps the entry's attributes as they were.
//
// In a build with the dispatch, the entry tests `LEVEL` and tail-calls `fma_copy`, the body with
// `FMA = true` compiled with the target feature `fma`. The first call, and every call on a CPU
// without `fma`, goes to `slow`, which detects the feature and calls the entry again where the
// CPU has it, and `dekker_copy` (`FMA = false`) where it does not. For an entry with a run-time
// `up`, `fma_copy` takes `UP` as a constant, so that a caller with a constant direction, inlining
// the entry (`#[cfg_attr(inari_kernel_dispatch, inline(always))]` on it), calls its own copy.
macro_rules! level_entry {
    // The direction is a constant `UP`.
    (
        $(#[$attr:meta])*
        $vis:vis fn $name:ident<const UP: bool>($($arg:ident: $ty:ty),*) -> $ret:ty = $with:ident;
    ) => {
        #[cfg(not(inari_kernel_dispatch))]
        $(#[$attr])*
        $vis fn $name<const UP: bool>($($arg: $ty),*) -> $ret {
            $with::<{ $crate::simd::HAS_FMA }, UP>($($arg),*)
        }

        #[cfg(inari_kernel_dispatch)]
        $(#[$attr])*
        $vis fn $name<const UP: bool>($($arg: $ty),*) -> $ret {
            #[target_feature(enable = "fma")]
            fn fma_copy<const UP: bool>($($arg: $ty),*) -> $ret {
                $with::<true, UP>($($arg),*)
            }
            // Out of line, so that its frame stays out of the entry.
            #[inline(never)]
            fn dekker_copy<const UP: bool>($($arg: $ty),*) -> $ret {
                $with::<false, UP>($($arg),*)
            }
            #[cold]
            #[inline(never)]
            fn slow<const UP: bool>($($arg: $ty),*) -> $ret {
                if $crate::dyadic::level::fma_detected() {
                    $name::<UP>($($arg),*)
                } else {
                    dekker_copy::<UP>($($arg),*)
                }
            }
            if $crate::dyadic::level::fma_ready() {
                // SAFETY: `LEVEL` is 2 only once `detect` has found `fma`.
                unsafe { fma_copy::<UP>($($arg),*) }
            } else {
                slow::<UP>($($arg),*)
            }
        }
    };

    // The direction is a run-time `up`, after one or two other arguments.
    (
        $(#[$attr:meta])*
        $vis:vis fn $name:ident($x:ident: $xty:ty, up: bool) -> $ret:ty = $with:ident;
    ) => {
        $crate::dyadic::level::level_entry! {
            @up $(#[$attr])* $vis fn $name[$x: $xty] -> $ret = $with;
        }
    };
    (
        $(#[$attr:meta])*
        $vis:vis fn $name:ident($x:ident: $xty:ty, $y:ident: $yty:ty, up: bool) -> $ret:ty =
            $with:ident;
    ) => {
        $crate::dyadic::level::level_entry! {
            @up $(#[$attr])* $vis fn $name[$x: $xty, $y: $yty] -> $ret = $with;
        }
    };
    (
        @up $(#[$attr:meta])*
        $vis:vis fn $name:ident[$($arg:ident: $ty:ty),*] -> $ret:ty = $with:ident;
    ) => {
        #[cfg(not(inari_kernel_dispatch))]
        $(#[$attr])*
        $vis fn $name($($arg: $ty,)* up: bool) -> $ret {
            $with::<{ $crate::simd::HAS_FMA }>($($arg,)* up)
        }

        #[cfg(inari_kernel_dispatch)]
        $(#[$attr])*
        $vis fn $name($($arg: $ty,)* up: bool) -> $ret {
            #[target_feature(enable = "fma")]
            fn fma_copy<const UP: bool>($($arg: $ty),*) -> $ret {
                $with::<true>($($arg,)* UP)
            }
            // Out of line, so that its frame stays out of the entry and its callers.
            #[inline(never)]
            fn dekker_copy($($arg: $ty,)* up: bool) -> $ret {
                $with::<false>($($arg,)* up)
            }
            #[cold]
            #[inline(never)]
            fn slow($($arg: $ty,)* up: bool) -> $ret {
                if $crate::dyadic::level::fma_detected() {
                    $name($($arg,)* up)
                } else {
                    dekker_copy($($arg,)* up)
                }
            }
            if $crate::dyadic::level::fma_ready() {
                // SAFETY: `LEVEL` is 2 only once `detect` has found `fma`.
                unsafe {
                    if up {
                        fma_copy::<true>($($arg),*)
                    } else {
                        fma_copy::<false>($($arg),*)
                    }
                }
            } else {
                slow($($arg,)* up)
            }
        }
    };

    // Rounded to nearest: no direction.
    (
        $(#[$attr:meta])*
        $vis:vis fn $name:ident($($arg:ident: $ty:ty),*) -> $ret:ty = $with:ident;
    ) => {
        #[cfg(not(inari_kernel_dispatch))]
        $(#[$attr])*
        $vis fn $name($($arg: $ty),*) -> $ret {
            $with::<{ $crate::simd::HAS_FMA }>($($arg),*)
        }

        #[cfg(inari_kernel_dispatch)]
        $(#[$attr])*
        $vis fn $name($($arg: $ty),*) -> $ret {
            #[target_feature(enable = "fma")]
            fn fma_copy($($arg: $ty),*) -> $ret {
                $with::<true>($($arg),*)
            }
            // Out of line, so that its frame stays out of the entry.
            #[inline(never)]
            fn dekker_copy($($arg: $ty),*) -> $ret {
                $with::<false>($($arg),*)
            }
            #[cold]
            #[inline(never)]
            fn slow($($arg: $ty),*) -> $ret {
                if $crate::dyadic::level::fma_detected() {
                    $name($($arg),*)
                } else {
                    dekker_copy($($arg),*)
                }
            }
            if $crate::dyadic::level::fma_ready() {
                // SAFETY: `LEVEL` is 2 only once `detect` has found `fma`.
                unsafe { fma_copy($($arg),*) }
            } else {
                slow($($arg),*)
            }
        }
    };
}

pub(super) use level_entry;
