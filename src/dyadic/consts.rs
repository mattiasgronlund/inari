// ln 2, ln 10 and π for the reductions of the elementary functions of the dyadic kernel, at the
// precision of each level of Ziv's strategy, from tables of 4,224 bits.
//
// The tables of ln 2 and ln 10 were computed with integers from the series ln 2 = 2 atanh(1/3)
// and ln 10 = 3 ln 2 + 2 atanh(1/9), atanh(x) = x + x^3 / 3 + x^5 / 5 + ..., at 4,288 bits,
// where the error of the sums leaves each bit that the tables keep unambiguous, and checked
// against `Decimal.ln()` of Python at 1,400 digits. The table of π is the floor of MPFR's π
// rounded down and up at 4,300 bits, which `pi_table` of `src/dyadic/atan/tests.rs` computes
// with `rug` and compares with it. `rocq/theories/Model.v` transcribes the tables and `split`,
// `rocq/theories/DyConst.v` proves the bounds that the comments of ln 2 and ln 10 state, and
// `rocq/theories/DyConstPi.v` that of π, from Machin's formula
// π / 4 = 4 atan(1/5) - atan(1/239).

use super::{round, Dyadic, Encl};
use crate::limbs;

// floor(ln 2 * 2^4224), in limbs, the least significant first.
const LN2: [u64; 66] = [
    0xc0b1_b31d_8a0e_23fa,
    0x85db_6ab0_3a49_bd0d,
    0x175e_b4af_c8da_add8,
    0xf07a_fff3_a892_374e,
    0x8f68_2625_0dea_891e,
    0xcecb_72f1_9c38_339d,
    0x5f6f_7ceb_ac9f_45ae,
    0x6c47_2096_e761_15c0,
    0x972c_d18b_fbbd_9d42,
    0x0ab1_11bb_bd67_c724,
    0x4738_26fd_a0c2_38b9,
    0x61c1_696d_d24a_aebd,
    0x156e_0c29_2413_d5e3,
    0x9518_4460_dc4e_7487,
    0xd762_2658_901e_646a,
    0xef2f_0ce2_d737_3958,
    0x2ac5_b61c_c4e9_207c,
    0x5733_9ba2_beba_7d05,
    0x0060_e499_0839_1a0c,
    0x6213_6319_6af5_0302,
    0x05c1_28d5_3d0b_d2f9,
    0x36e0_2b20_cee8_86b9,
    0x0bbb_16fa_f3d9_49f2,
    0x4221_83ed_c994_2109,
    0x5e92_22b8_8c66_d3c5,
    0x61af_fd44_6b1c_a3cf,
    0x268a_5c1f_9538_b982,
    0x8d6f_5177_fbcf_0755,
    0xa172_93d1_228a_4ef9,
    0x44a0_2554_731c_dc8e,
    0x96d4_e6d3_30af_889b,
    0x5570_b6c6_8f96_9834,
    0x7598_a195_1ae2_73ee,
    0x4d16_2db3_b365_853d,
    0x5f50_b518_5064_c18b,
    0x078f_735d_1b2d_b31b,
    0xae31_3cdb_6c60_6cb1,
    0x955d_5179_b1e1_7b9d,
    0x0c48_0a54_1735_0d2c,
    0x074d_b601_5cfe_7aa3,
    0x6a9c_7f8a_5e14_8e82,
    0x2566_9b33_3564_a337,
    0x4c1a_1e0b_d1d6_095d,
    0xcccc_4e65_9393_514c,
    0xc943_e732_b479_cd33,
    0x1746_0775_db89_90e5,
    0x7d2e_23de_1400_b396,
    0xee56_9d6d_fc1e_fa15,
    0x610d_30f8_8fe5_51a2,
    0x07f4_ca11_fb5b_fb90,
    0xda2d_97c5_0f3f_d5c6,
    0x655f_a187_2f20_e3a2,
    0xf5df_a6bd_3830_3248,
    0x72ce_87b1_9d65_48ca,
    0x256f_a0ec_7657_f74b,
    0xb9ea_9bc3_b136_603b,
    0x1acb_da11_317c_387e,
    0x3e96_ca16_224a_e8c5,
    0x2757_3b29_1169_b825,
    0xed2e_ae35_c138_2144,
    0x5595_52fb_4afa_1b10,
    0xe7b8_7620_6deb_ac98,
    0x8a0d_175b_8baa_fa2b,
    0x40f3_4326_7298_b62d,
    0xc9e3_b398_03f2_f6af,
    0xb172_17f7_d1cf_79ab,
];

// floor(ln 10 * 2^4222), in limbs, the least significant first.
const LN10: [u64; 66] = [
    0xfa9d_8c59_8c57_4502,
    0xfb5f_06c3_58ac_8f70,
    0x8e66_8aea_ba83_c7f8,
    0xb81c_4a5b_53d4_9ea6,
    0x48a9_3f5f_5e3b_6eb4,
    0xa2d6_fe91_388e_9e3e,
    0x4b40_ed7a_56c6_cdcd,
    0xc4b8_3301_006b_f062,
    0x1be5_a9a9_67fd_dc57,
    0xff30_65c4_0cfc_eec8,
    0x89bf_752f_b5df_b353,
    0x6a36_cecc_b2d5_ae5b,
    0xbc12_61c8_b3e4_daad,
    0xdf3c_cbb3_189d_a49d,
    0xd006_f8b4_be14_5a2a,
    0x99d6_d20e_a2de_fd2b,
    0xb652_4dc1_8c16_7e86,
    0xed69_b13d_c1a0_3730,
    0xf42c_58de_f8a3_c52d,
    0xf6ff_363d_b00b_6b33,
    0xa0d9_c260_794a_976f,
    0x421e_f5e0_b004_10a0,
    0xdef8_5a05_eb56_323a,
    0x8fcd_0832_4a7b_32a6,
    0x0a62_d18e_478f_7bd5,
    0x4d5e_843f_2064_2b97,
    0x1f1d_366c_2066_3834,
    0xbc64_ea80_6e19_8566,
    0xaa66_04a5_324e_c3dc,
    0xb5e4_b1c8_c0e5_a10a,
    0x3b70_fcda_2d73_2d47,
    0x0942_6178_1912_7a6e,
    0x3982_a78c_a45d_dfc8,
    0xef99_c8e5_f697_4f36,
    0x4cb0_466d_61ba_648e,
    0xad6b_fbff_d821_ba0a,
    0xe38a_5700_ffde_2db1,
    0xf77e_3760_4e94_3960,
    0xa949_eaaa_df69_e8a5,
    0xe880_47f1_7b0d_9b50,
    0x3848_c8d2_5faf_1bca,
    0x3dfd_3c51_748e_6d6e,
    0xaf88_486e_a9b7_401e,
    0xf47f_a96d_eb27_1060,
    0x4576_5cde_2683_39db,
    0xe40b_f3cc_1e14_126a,
    0xdb1d_28ea_57d4_fdc0,
    0xa47e_cb26_978c_5d4f,
    0x9cd5_b42e_6a27_1619,
    0xe247_8fca_ad3a_ee98,
    0x469e_a58e_9305_e981,
    0x5b08_b057_d5ed_e20f,
    0x8e93_368d_4478_9c4f,
    0xca67_b35b_2360_5085,
    0x5161_bb49_d219_c7bb,
    0xef66_ceb0_4ab3_c6fa,
    0x765a_a6c3_b0d8_31fb,
    0x782c_f8a2_8a8c_911e,
    0xfb8f_7884_02e5_16d6,
    0x2c62_2418_410b_e2da,
    0xcc70_cbc0_2c5f_0d68,
    0x962f_02d7_b1a8_105c,
    0x83c6_1e82_01f0_2d72,
    0xe28f_ecf9_da5d_f90e,
    0xea56_d62b_82d3_0a28,
    0x935d_8ddd_aaa8_ac16,
];

// floor(π * 2^4222), in limbs, the least significant first. `pub(super)` for `reduce` of
// `src/dyadic/trig.rs`, which divides by its top limbs, and for `pi_table` of
// `src/dyadic/atan/tests.rs`, which checks it.
pub(super) const PI: [u64; 66] = [
    0xf8ff_9406_ad9e_530e,
    0xc975_1e76_3dba_37bd,
    0xc1d4_dcb2_6026_46de,
    0x36c3_fab4_d27c_7026,
    0x4df4_35c9_3402_8492,
    0x86ff_b7dc_90a6_c08f,
    0x93b4_ea98_8d8f_ddc1,
    0xd006_9127_d5b0_5aa9,
    0xb81b_dd76_2170_481c,
    0x1f61_2970_cee2_d7af,
    0x233b_a186_515b_e7ed,
    0x99b2_964f_a090_c3a2,
    0x287c_5947_4e6b_c05d,
    0x2e8e_fc14_1fbe_caa6,
    0xdbbb_c2db_04de_8ef9,
    0x2583_e9ca_2ad4_4ce8,
    0x1a94_6834_b615_0bda,
    0x99c3_2718_6af4_e23c,
    0x8871_9a10_bdba_5b26,
    0x1a72_3c12_a787_e6d7,
    0x4b82_d120_a921_0801,
    0x43db_5bfc_e0fd_108e,
    0x08e2_4fa0_74e5_ab31,
    0x7709_88c0_bad9_46e2,
    0xbbe1_1757_7a61_5d6c,
    0x521f_2b18_177b_200c,
    0xd876_0273_3ec8_6a64,
    0xf12f_fa06_d98a_0864,
    0xcee3_d226_1ad2_ee6b,
    0x1e8c_94e0_4a25_619d,
    0xabf5_ae8c_db09_33d7,
    0xb397_0f85_a6e1_e4c7,
    0x8aea_7157_5d06_0c7d,
    0xecfb_8504_58db_ef0a,
    0xa855_21ab_df1c_ba64,
    0xad33_170d_0450_7a33,
    0x1572_8e5a_8aaa_c42d,
    0x15d2_2618_98fa_0510,
    0x3995_497c_ea95_6ae5,
    0xde2b_cbf6_9558_1718,
    0xb5c5_5df0_6f4c_52c9,
    0x9b27_83a2_ec07_a28f,
    0xe39e_772c_180e_8603,
    0x3290_5e46_2e36_ce3b,
    0xf174_6c08_ca18_217c,
    0x670c_354e_4abc_9804,
    0x9ed5_2907_7096_966d,
    0x1c62_f356_2085_52bb,
    0x8365_5d23_dca3_ad96,
    0x6916_3fa8_fd24_cf5f,
    0x98da_4836_1c55_d39a,
    0xc200_7cb8_a163_bf05,
    0x4928_6651_ece4_5b3d,
    0xae9f_2411_7c4b_1fe6,
    0xee38_6bfb_5a89_9fa5,
    0x0bff_5cb6_f406_b7ed,
    0xf44c_42e9_a637_ed6b,
    0xe485_b576_625e_7ec6,
    0x4fe1_356d_6d51_c245,
    0x302b_0a6d_f25f_1437,
    0xef95_19b3_cd3a_431b,
    0x514a_0879_8e34_04dd,
    0x020b_bea6_3b13_9b22,
    0x2902_4e08_8a67_cc74,
    0xc4c6_628b_80dc_1cd1,
    0xc90f_daa2_2168_c234,
];

// A constant c that `t` gives as T * 2^e <= c < (T + 1) * 2^e, for the integer T of 4,224 bits
// whose limbs `t` holds, the least significant first, split into c = h + l: the `Dyadic<N>`
// h of the top 64 N - z bits of T, and an enclosure of l. The low z bits of the mantissa of h
// are 0, so that h times an integer below 2^z is exact at 64 N bits.
fn split<const N: usize>(t: &[u64; 66], e: i64, z: u32) -> (Dyadic<N>, Encl<N>) {
    // T = H * 2^(64 (66 - N)) + w, for the top N limbs H of T without their low z bits, and
    // the window w of the limbs below them and of those z bits. The top bit of T is set, so
    // that h = H * 2^(e + 64 (66 - N)) is normalized.
    let mut m = [0; N];
    m.copy_from_slice(&t[66 - N..]);
    m[0] &= u64::MAX << z;
    let h = Dyadic {
        neg: false,
        exp: e + 64 * (66 - N) as i64,
        m,
    };
    let mut w = [0; 67];
    w[..67 - N].copy_from_slice(&t[..67 - N]);
    w[66 - N] &= (1 << z) - 1;
    // l is in [w * 2^e, (w + 1) * 2^e). The limb above the window takes the carry of w + 1.
    let lo = round(false, &w[..67 - N], e, false, false);
    limbs::add_assign(&mut w[..68 - N], &[1]);
    let hi = round(false, &w[..68 - N], e, false, true);
    (h, Encl { lo, hi })
}

/// ln 2 = h + l for `(h, l)`, where `l` encloses l, and h has 64 N - 12 bits, so that h times
/// an integer below 2^12 is exact.
pub(crate) fn ln2<const N: usize>() -> (Dyadic<N>, Encl<N>) {
    split(&LN2, -4224, 12)
}

/// ln 10 = h + l for `(h, l)`, where `l` encloses l, and h has 64 N - 53 bits, so that h times
/// an `f64` is exact.
pub(crate) fn ln10<const N: usize>() -> (Dyadic<N>, Encl<N>) {
    split(&LN10, -4222, 53)
}

/// An enclosure of π: [h, h + 2^-(64 N - 2)] for the h of the top 64 N bits of its table, as
/// π / 2^-4222 has 4,224 bits, the top one set. Its callers shift it, add it and multiply it
/// by an `f64` with `Encl::mul`, which rounds, so that none needs h times an integer to be
/// exact, as those of ln 2 and ln 10 do, and h keeps all of its bits.
pub(crate) fn pi<const N: usize>() -> Encl<N> {
    let (h, l) = split(&PI, -4222, 0);
    Encl { lo: h, hi: h }.add(&l)
}
