// The table `INV2PI` of the fast path of `src/dyadic/trig.rs`, as `u64`s; its table `SC` is
// in `src/dyadic/trig/sc_table.rs`, which a test generates. `INV2PI` holds the bits of 1/(2π)
// for the reduction of large arguments; `rocq/theories/FastTrigBigInt.v` proves that, read as
// one integer T, T <= 2^1216 / (2π) <= T + 1, from the bits of π in `src/dyadic/consts.rs`
// (`inv2pi_bounds`), and the tests check that T is floor(2^1216 / (2π)) against MPFR.
//
// `rocq/theories/Model.v` transcribes the table (`DyadicTrig.INV2PI`), so it has to be updated
// along with it.

/// The bits of 1/(2π) down to 2^-1216, floor(2^1216 / (2π)), as 20 limbs from the most
/// significant: bit j from the top, for j from 0 to 1279, is the bit of 2^(63 - j) in 1/(2π),
/// so that the first 64 are 0.
pub(super) const INV2PI: [u64; 20] = [
    0x0000_0000_0000_0000,
    0x28be_60db_9391_054a,
    0x7f09_d5f4_7d4d_3770,
    0x36d8_a566_4f10_e410,
    0x7f94_58ea_f7ae_f158,
    0x6dc9_1b8e_9093_74b8,
    0x0192_4bba_8274_6487,
    0x3f87_7ac7_2c4a_69cf,
    0xba20_8d7d_4bae_d121,
    0x3a67_1c09_ad17_df90,
    0x4e64_758e_60d4_ce7d,
    0x2721_17e2_ef7e_4a0e,
    0xc7fe_25ff_f781_6603,
    0xfbcb_c462_d682_9b47,
    0xdb4d_9fb3_c9f2_c26d,
    0xd3d1_8fd9_a797_fa8b,
    0x5d49_eeb1_faf9_7c5e,
    0xcf41_ce7d_e294_a4ba,
    0x9afe_d7ec_47e3_5742,
    0x1580_cc11_bf1e_daea,
];
