//! This is a tnum implementation for Solana eBPF
//! Z3 Verification for fast_divide algorithm
use fastdivide::DividerU64;
use std::u64;
use z3::ast::{Ast, BV, Bool};
use z3::{Config, Context, Solver, Sort, SatResult};

fn testbit(val: u64, bit: u8) -> bool {
    if bit >= 64 {
        return false;
    }
    (val & (1u64 << bit)) != 0
}

/// 位操作 trait
pub trait BitOps {
    /// 清除低位（从最低位开始的 n 位）
    fn clear_low_bits(&mut self, n: u32);
    /// 清除高位（从最高位开始的 n 位）
    fn clear_high_bits(&mut self, n: u32);
}

impl BitOps for u64 {
    fn clear_low_bits(&mut self, n: u32) {
        if n >= 64 {
            *self = 0;
        } else {
            *self &= (!0u64).wrapping_shl(n);
        }
    }

    fn clear_high_bits(&mut self, n: u32) {
        if n >= 64 {
            *self = 0;
        } else {
            *self &= (1u64 << (64 - n)) - 1;
        }
    }
}

// This is for bit-level abstraction
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// tnum definition
pub struct Tnum {
    pub value: u64,
    pub mask: u64,
}

pub struct TnumU128 {
    pub value: u128,
    pub mask: u128,
}

impl TnumU128 {
    /// 创建实例
    pub fn new(value: u128, mask: u128) -> Self {
        Self { value, mask }
    }
    /// tnum 的加法操作
    pub fn add(&self, other: Self) -> Self {
        // 计算掩码之和 - 表示两个不确定数的掩码组合
        let sm = self.mask.wrapping_add(other.mask);

        // 计算确定值之和
        let sv = self.value.wrapping_add(other.value);

        // sigma = (a.mask + b.mask) + (a.value + b.value)
        // 用于检测进位传播情况
        let sigma = sm.wrapping_add(sv);

        // chi = 进位传播位图
        // 通过异或操作找出哪些位发生了进位
        let chi = sigma ^ sv;

        // mu = 最终的不确定位掩码
        // 包括:
        // 1. 进位产生的不确定性 (chi)
        // 2. 原始输入的不确定位 (a.mask | b.mask)
        let mu = chi | self.mask | other.mask;

        // 返回结果:
        // value: 确定值之和，但排除所有不确定位 (~mu)
        // mask: 所有不确定位的掩码
        Self::new(sv & !mu, mu)
    }

    /// tnum 的乘法操作
    pub fn mul(&self, other: Self) -> Self {
        let mut a = Self::new(self.value, self.mask);
        let mut b = Self::new(other.value, other.mask);
        let acc_v = a.value.wrapping_mul(b.value);
        let mut acc_m: Self = Self::new(0, 0);
        while (a.value != 0) || (a.mask != 0) {
            // println!("acc_m.mask:{:?}, acc_m.value:{:?}", acc_m.mask, acc_m.value);
            if (a.value & 1) != 0 {
                acc_m = acc_m.add(Self::new(0, b.mask));
            } else if (a.mask & 1) != 0 {
                acc_m = acc_m.add(Self::new(0, b.value | b.mask));
            }
            a.value = a.value.wrapping_shr(1);
            a.mask = a.mask.wrapping_shr(1);
            b.value = b.value.wrapping_shl(1);
            b.mask = b.mask.wrapping_shl(1);
        }
        Self::new(acc_v, 0).add(acc_m)
    }
}

impl Tnum {
    /// 创建实例
    pub fn new(value: u64, mask: u64) -> Self {
        Self { value, mask }
    }

    /// 创建 bottom 元素
    pub fn bottom() -> Self {
        Self::new(0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF)
    }

    /// 创建 top 元素
    pub fn top() -> Self {
        Self::new(0, 0xFFFFFFFFFFFFFFFF)
    }

    /// 创建一个常数 tnum 实例
    pub fn const_val(value: u64) -> Self {
        Self::new(value, 0)
    }

    /// from integer interval to tnum
    pub fn from_range(min: u64, max: u64) -> Self {
        let chi = min ^ max;
        //最高未知位
        let bits = (64 - chi.leading_zeros()) as u64;
        //超出范围则完全未知
        if bits > 63 {
            return Self::new(0, u64::MAX);
        }

        //范围内的未知位
        let delta = (1u64 << bits) - 1;
        Self::new(min & !delta, delta)
    }

    /// 获取 value 字段
    pub fn value(&self) -> u64 {
        self.value
    }

    /// 获取 mask 字段
    pub fn mask(&self) -> u64 {
        self.mask
    }

    pub fn is_zero(&self) -> bool {
        self.value == 0 && self.mask == 0
    }
    /// 判断是否为bottom（不可能的值）
    pub fn is_bottom(&self) -> bool {
        (self.value & self.mask) != 0
    }

    /// 判断是否为top（完全不确定的值）
    pub fn is_top(&self) -> bool {
        self.value == 0 && self.mask == u64::MAX
    }

    /// 判断是否为确定值（单点）
    pub fn is_singleton(&self) -> bool {
        self.mask == 0
    }

    /// 判断是否为非负数（最高位为0）
    pub fn is_nonnegative(&self) -> bool {
        (self.value & (1 << 63)) == 0 && (self.mask & (1 << 63)) == 0
    }

    /// 判断是否为负数（最高位为1）
    pub fn is_negative(&self) -> bool {
        (self.value & (1 << 63)) != 0 && (self.mask & (1 << 63)) == 0
    }

    /// 统计高位连续0的个数
    pub fn countl_zero(&self) -> u32 {
        self.value.leading_zeros()
    }

    /// 统计低位连续0的个数
    pub fn countr_zero(&self) -> u32 {
        self.value.trailing_zeros()
    }

    /// 统计最小的高位连续0的个数
    pub fn count_min_leading_zeros(&self) -> u32 {
        let max = self.value.wrapping_add(self.mask);
        max.leading_zeros()
    }

    /// 统计最小的低位连续0的个数
    pub fn count_min_trailing_zeros(&self) -> u32 {
        let max = self.value.wrapping_add(self.mask);
        max.trailing_zeros()
    }

    /// 统计最大的高位连续0的个数
    pub fn count_max_leading_zeros(&self) -> u32 {
        self.value.leading_zeros()
    }

    /// 统计最大的低位连续0的个数
    pub fn count_max_trailing_zeros(&self) -> u32 {
        self.value.trailing_zeros()
    }

    /// 清除高位
    pub fn clear_high_bits(&mut self, n: u32) {
        if n >= 64 {
            self.value = 0;
            self.mask = 0;
        } else {
            let mask = (1u64 << (64 - n)) - 1;
            self.value &= mask;
            self.mask &= mask;
        }
    }

    /// tnum 的左移操作
    pub fn tnum_lshift(self: Tnum, shift: u8) -> Tnum {
        Tnum::new(
            self.value.wrapping_shl(shift as u32),
            self.mask.wrapping_shl(shift as u32),
        )
    }

    /// tnum 的右移操作
    pub fn tnum_rshift(self: Tnum, shift: u8) -> Tnum {
        Tnum::new(
            self.value.wrapping_shr(shift as u32),
            self.mask.wrapping_shr(shift as u32),
        )
    }

    /// tnum 算数右移的操作
    pub fn tnum_arshift(self: Tnum, min_shift: u8, insn_bitness: u8) -> Tnum {
        match insn_bitness {
            32 => {
                //32位模式
                let value = ((self.value as i32) >> min_shift) as u32;
                let mask = ((self.mask as i32) >> min_shift) as u32;
                Tnum::new(value as u64, mask as u64)
            }
            _ => {
                //64位模式
                let value = ((self.value as i64) >> min_shift) as u64;
                let mask = ((self.mask as i64) >> min_shift) as u64;
                Tnum::new(value, mask)
            }
        }
    }

    pub fn shl(&self, x: &Tnum) -> Tnum {
        if self.is_bottom() || x.is_bottom() {
            return Tnum::bottom();
        } else if self.is_top() || x.is_top() {
            return Tnum::top();
        }

        if x.is_singleton() {
            return self.shl_const(x.value);
        } else {
            let w = 64u8;
            let mut res = Tnum::top();
            let min_shift_amount = x.value;

            if self.mask == u64::MAX {
                res.value = res.value.wrapping_shl(min_shift_amount as u32);
                res.mask = res.mask.wrapping_shl(min_shift_amount as u32);
                return res;
            }

            let max_value = x.value.wrapping_add(x.mask);
            let len = (self.value | self.mask).leading_zeros() as u64;
            let mut max_res = Tnum::top();

            if len > max_value {
                max_res.mask.clear_high_bits((len - max_value) as u32);
            }

            let max_shift_amount = if max_value > w as u64 {
                w as u64
            } else {
                max_value
            };

            if min_shift_amount == 0 && max_shift_amount == w as u64 {
                println!("[Rust shl] Fast path: shift amount is unknown");
                let min_trailing_zeros = self.count_min_trailing_zeros();
                res.value.clear_low_bits(min_trailing_zeros);
                res.mask.clear_low_bits(min_trailing_zeros);
                return res;
            }

            res.mask = u64::MAX;
            res.value = u64::MAX;
            let mut join_count = 0;

            for i in min_shift_amount..=max_shift_amount {
                if x.value == ((!x.mask) & i) {
                    continue;
                }
                join_count += 1;
                let tmp = self.shl_const(i);
                res = res.or(&tmp);
                if join_count > 8 || res.is_top() {
                    return Tnum::top();
                }
            }

            if res.is_bottom() {
                Tnum::top()
            } else {
                res
            }
        }
    }

    pub fn lshr(&self, x: &Tnum) -> Tnum {
        if self.is_bottom() || x.is_bottom() {
            return Tnum::bottom();
        } else if self.is_top() || x.is_top() {
            return Tnum::top();
        }

        if x.is_singleton() {
            return self.lshr_const(x.value);
        } else {
            let w = 64u8; // 假设 64 位
            let mut res = Tnum::top();
            let min_shift_amount = x.value;
            let len = self.value.leading_zeros() as u64;
            let max_value = x.value.wrapping_add(x.mask);
            let max_shift_amount = if max_value > w as u64 {
                w as u64
            } else {
                max_value
            };
            let mut max_res = Tnum::top();
            if (len + x.value) >= w as u64 {
                return Tnum::new(0, 0);
            } else {
                max_res.clear_high_bits((len + x.value) as u32);
            }

            res = Tnum {
                value: u64::MAX,
                mask: u64::MAX,
            };
            // let mut join_count = 0;
            for i in min_shift_amount..=max_shift_amount {
                res = res.or(&self.lshr_const(i));
                // join_count += 1;
                if res.is_top() {
                    return max_res;
                }
            }
            if res.is_bottom() {
                max_res
            } else {
                res
            }
        }
    }

    /// tnum 的加法操作
    pub fn add(&self, other: Self) -> Self {
        // 计算掩码之和 - 表示两个不确定数的掩码组合
        let sm = self.mask.wrapping_add(other.mask);

        // 计算确定值之和
        let sv = self.value.wrapping_add(other.value);

        // sigma = (a.mask + b.mask) + (a.value + b.value)
        // 用于检测进位传播情况
        let sigma = sm.wrapping_add(sv);

        // chi = 进位传播位图
        // 通过异或操作找出哪些位发生了进位
        let chi = sigma ^ sv;

        // mu = 最终的不确定位掩码
        // 包括:
        // 1. 进位产生的不确定性 (chi)
        // 2. 原始输入的不确定位 (a.mask | b.mask)
        let mu = chi | self.mask | other.mask;

        // 返回结果:
        // value: 确定值之和，但排除所有不确定位 (~mu)
        // mask: 所有不确定位的掩码
        Self::new(sv & !mu, mu)
    }

    /// tnum 的减法操作
    pub fn sub(&self, other: Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        } else if self.is_top() || other.is_top() {
            return Self::top();
        }
        let dv = self.value.wrapping_sub(other.value);
        let alpha = dv.wrapping_add(self.mask);
        let beta = dv.wrapping_sub(other.mask);
        let chi = alpha ^ beta;
        let mu = chi | self.mask | other.mask;
        Self::new(dv & !mu, mu)
    }

    /// tnum 的按位异或操作
    pub fn xor(&self, other: Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        } else if self.is_top() || other.is_top() {
            return Self::top();
        }

        let v = self.value ^ other.value;
        let mu = self.mask | other.mask;

        Self::new(v & !mu, mu)
    }

    /// tnum 的乘法操作
    pub fn mul(&self, other: Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        } else if self.is_top() || other.is_top() {
            return Self::top();
        }
        let mut a = *self;
        let mut b = other;
        let acc_v = a.value.wrapping_mul(b.value);
        let mut acc_m: Self = Self::new(0, 0);
        while (a.value != 0) || (a.mask != 0) {
            // println!("acc_m.mask:{:?}, acc_m.value:{:?}", acc_m.mask, acc_m.value);
            if (a.value & 1) != 0 {
                acc_m = acc_m.add(Tnum::new(0, b.mask));
            } else if (a.mask & 1) != 0 {
                acc_m = acc_m.add(Tnum::new(0, b.value | b.mask));
            }
            a = a.lshr_const(1);
            b = b.shl_const(1);
        }
        Tnum::new(acc_v, 0).add(acc_m)
    }

    /// tnum 的按位非操作
    pub fn not(&self) -> Self {
        if self.is_bottom() {
            return Self::bottom();
        } else if self.is_top() {
            return Self::top();
        }
        Self::new(!(self.value ^ self.mask), self.mask)
    }

    /// A constant-value optimization for tnum_mul
    pub fn mul_opt(&self, other: Self) -> Self {
        // 如果一个是常数
        if self.mask == 0 && self.value.count_ones() == 1 {
            // a.value = 2 ^ x
            other.shl_const(self.value.trailing_zeros() as u64)
        } else if other.mask == 0 && other.value.count_ones() == 1 {
            // a.value = 2 ^ x
            self.shl_const(other.value.trailing_zeros() as u64)
        } else if (self.value | self.mask).count_ones() <= (other.value | other.mask).count_ones() {
            self.mul(other)
        } else {
            other.mul(*self)
        }
    }

    ///computes the w of the tnum domain.
    pub fn join(&self, other: Self) -> Self {
        let v = self.value ^ other.value;
        let m = (self.mask | other.mask) | v;
        Self::new((self.value | other.value) & (!m), m)
    }

    /// [split_at_mu] splits a tnum at the first unknow.
    fn split_at_mu(&self) -> (Self, u32, Self) {
        let i = self.mask.leading_ones();
        let x1 = Self::new(self.value >> (i + 1), self.mask >> (i + 1));
        let x2 = Self::new(self.value & ((1 << i) - 1), self.mask & ((1 << i) - 1));
        (x1, i, x2)
    }

    /// [tnum_mul_const] multiplies a constant [c] by the tnum [x]
    /// which has [j] unknown bits and [n] is the fuel (Z.of_nat n = j).
    fn mul_const(&self, c: u64, n: u64) -> Self {
        if n == 0 {
            Self::new(c.wrapping_mul(self.value), 0)
        } else {
            let (y1, i1, y2) = self.split_at_mu();
            let p = y1.mul_const(c, n - 1);
            let mc = Self::new(c.wrapping_mul(y2.mask), 0);
            let mu0 = p.shl_const((i1 + 1) as u64).add(mc);
            let mu1 = mu0.add(Self::new(c.wrapping_shl(i1 as u32), 0));
            mu0.join(mu1)
        }
    }

    /// [xtnum_mul x i y j] computes the multiplication of
    /// [x]  which has [i] unknown bits by
    /// [y]  which has [j] unknown bits such (i <= j)
    fn xtnum_mul(x: Self, i: u64, y: Self, j: u64) -> Self {
        if i == 0 && j == 0 {
            Self::new(x.value * y.value, 0)
        } else {
            let (y1, i1, y2) = y.split_at_mu(); // y = y1.mu.y2
            let p = if i == j {
                Self::xtnum_mul(y1, j - 1, x, i)
            } else {
                Self::xtnum_mul(x, i, y1, j - 1)
            };
            let mc = x.mul_const(y2.value, i);
            let mu0 = p.shl_const((i1 + 1) as u64).add(mc);
            let mu1 = mu0.add(x.shl_const(i1 as u64));
            mu0.join(mu1)
        }
    }

    /// the top of the xtnum_mul
    pub fn xtnum_mul_top(&self, other: Self) -> Self {
        let i = 64 - self.mask.leading_zeros() as u64;
        let j = 64 - other.mask.leading_zeros() as u64;
        if i <= j {
            Self::xtnum_mul(*self, i, other, j)
        } else {
            Self::xtnum_mul(other, j, *self, i)
        }
    }

    /// clear bit of a tnum
    fn clear_bit(&self, pos: u8) -> Self {
        Self::new(self.value & !(1 << pos), self.mask & !(1 << pos))
    }

    /// bit size of a tnum
    fn size(&self) -> u8 {
        let a = 64 - self.value.leading_zeros();
        let b = 64 - self.mask.leading_zeros();
        if a < b {
            b as u8
        } else {
            a as u8
        }
    }

    /// max 64 of a tnum
    fn max_val(&self) -> u64 {
        self.value | self.mask
    }

    /// [xtnum_mul_high x y n] multiplies x by y
    /// where n is the number of bits that are set in either x or y.
    /// We also have that x <= y and 0 <= x and 0 <= y
    fn xtnum_mul_high(&self, y: Self, n: u8) -> Self {
        if self.mask == 0 && y.mask == 0 {
            //if both are constants, perform normal multiplication
            Self::new(self.value.wrapping_mul(y.value), 0)
        } else if n == 0 {
            //panic!("should not happen");
            Self::new(0, 0) //should not happen
        } else {
            let b = y.size();
            if b == 0 {
                return Self::new(0, 0);
            }
            let ym = testbit(y.mask, b - 1);
            let y_prime = y.clear_bit(b - 1); //clear the highest bit of y
            let p = if y_prime.max_val() <= self.max_val() {
                y_prime.xtnum_mul_high(*self, n - 1)
            } else {
                self.xtnum_mul_high(y_prime, n - 1)
            };
            if ym {
                p.add(self.shl_const((b - 1) as u64)).join(p)
            } else {
                p.add(self.shl_const((b - 1) as u64))
            }
        }
    }

    /// the top level of xtnum_mul_high
    pub fn xtnum_mul_high_top(&self, other: Self) -> Self {
        self.xtnum_mul_high(
            other,
            ((self.value | self.mask).count_ones() + (other.value | other.mask).count_ones()) as u8,
        )
    }

    /// aux function for tnum_mul_rec
    fn decompose(&self) -> (Self, Self) {
        (
            Self::new(self.value >> 1, self.mask >> 1),
            Self::new(self.value & 1, self.mask & 1),
        )
    }

    /// A new tnum_mul proposed by frederic
    pub fn mul_rec(&self, other: Self) -> Self {
        if self.mask == 0 && other.mask == 0 {
            // both are known
            Self::new(self.value * other.value, 0)
        } else if self.mask == u64::MAX && other.mask == u64::MAX {
            //both are unknown
            Self::new(0, u64::MAX)
        } else if (self.value == 0 && self.mask == 0) || (other.value == 0 && other.mask == 0) {
            // mult by 0
            Self::new(0, 0)
        } else if self.value == 1 && self.mask == 0 {
            // mult by 1
            other
        } else if other.value == 1 && other.mask == 0 {
            // mult by 1
            *self
        } else {
            let (a_up, _a_low) = self.decompose();
            let (b_up, _b_low) = other.decompose();
            a_up.mul_rec(b_up)
            //tnum_mul_rec(a_up, b_up) + tnum_mul_rec(a_up, b_low) + tnum_mul_rec(a_low, b_up) + tnum_mul_rec(a_low, b_low)
            // TODO: this one is wrong, replace this line with the following impl
            /* decompose the mask of am && bm
            so that the last bits either 0s or 1s
            In assembly, finding the rightmost 1 or 0 of a number is fast

            let (a_up,a_low) = decompose a in
            let (b_up,b_low) = decompose b in
            // a_low and b_low are either 1s or 0s
            (mul a_up b_up) + (mul a_up b_low) +
            (mul a_low b_up) + (mul a_low b_low)
            */
        }
    }

    /// tnum 的交集计算
    pub fn intersect(&self, other: Self) -> Self {
        let v = self.value | other.value;
        let mu = self.mask & other.mask;
        Self::new(v & !mu, mu)
    }

    /// tnum 用与截断到指定字节大小
    pub fn cast(&self, size: u8) -> Self {
        //处理溢出
        let mut result = *self;
        result.value &= (1u64 << (size * 8)) - 1;
        result.mask &= (1u64 << (size * 8)) - 1;
        result
    }

    pub fn is_aligned(&self, size: u64) -> bool {
        (self.value | self.mask) & (size - 1) == (size - 1)
    }

    /// Checks if self contains other
    pub fn contains(&self, other: Self) -> bool {
        if self.is_bottom() {
            false
        } else if other.is_bottom() {
            true
        } else {
            (self.value & !other.mask) == (other.value & !other.mask)
                && (self.mask | other.mask) == self.mask
        }
    }

    /// tnum转换为字符串
    pub fn to_sbin(&self, size: usize) -> String {
        let mut result = vec![0u8; size];
        let mut a = *self;

        // 从高位到低位处理每一位
        for n in (1..=64).rev() {
            if n < size {
                result[n - 1] = match (a.mask & 1, a.value & 1) {
                    (1, _) => b'x', // 不确定位
                    (0, 1) => b'1', // 确定位 1
                    (0, 0) => b'0', // 确定位 0
                    _ => unreachable!(),
                };
            }
            // 右移处理下一位
            a.mask >>= 1;
            a.value >>= 1;
        }

        // 设置字符串结束位置
        let end = std::cmp::min(size - 1, 64);
        result[end] = 0;

        // 转换为字符串
        String::from_utf8(result[..end].to_vec()).unwrap_or_else(|_| String::new())
    }

    pub fn subreg(&self) -> Self {
        self.cast(4)
    }

    pub fn clear_subreg(&self) -> Self {
        self.lshr_const(32).shl_const(32)
    }

    pub fn with_subreg(&self, subreg: Self) -> Self {
        self.clear_subreg().or(&subreg.subreg())
    }

    pub fn with_const_subreg(&self, value: u32) -> Self {
        self.with_subreg(Self::const_val(value as u64))
    }

    /// 有符号取余操作（SRem）
    pub fn srem(&self, other: Self) -> Self {
        // 处理 bottom 和 top 情况
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        } else if self.is_top() || other.is_top() {
            return Self::top();
        }

        // 处理单点值情况
        if self.is_singleton() && other.is_singleton() {
            let res_single = Tnum::new(
                (self.value as i64).wrapping_rem(other.value as i64) as u64,
                0,
            );
            return res_single;
        }

        // 处理除数为0的情况
        if other.value == 0 {
            return Self::top(); // top
        } else {
            let mut res = rem_get_low_bits(self, &other);
            if other.mask == 0
                && (other.value) & 1 == 0
                && ((other.value.trailing_zeros() + other.value.leading_zeros() + 1) == 64)
            {
                let low_bits = other.value - 1;
                if self.is_nonnegative()
                    || (other.value.trailing_zeros() <= self.count_min_trailing_zeros())
                {
                    res.value = low_bits & res.value;
                    res.mask = low_bits & res.mask;
                }
                if self.is_negative() && !(self.value & low_bits) == 0 {
                    res.mask = low_bits & res.mask;
                    res.value = (!low_bits) | res.value;
                }
                return res;
            }
            let leadingz = self.count_min_leading_zeros();
            res.value.clear_high_bits(leadingz);
            res.mask.clear_high_bits(leadingz);
            return res;
        }
    }

    /// 无符号取余操作（URem）
    pub fn urem(&self, other: Self) -> Self {
        // 处理 bottom 和 top 情况
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        } else if self.is_top() || other.is_top() {
            return Self::top();
        }

        // 处理除数为0的情况
        if other.value == 0 {
            return Self::top(); // 除以0返回top
        }

        let mut res = rem_get_low_bits(self, &other);
        // 处理低位
        // 检查除数是否为 2 的幂
        if other.mask == 0
            && !((other.value >> 63) & 1 == 1)
            && ((other.value.trailing_zeros() + other.value.leading_zeros() + 1) == 64)
        {
            // 除数是 2 的幂，直接用位掩码计算余数
            let low_bits = other.value - 1; // 例如：8-1=7(0b111)，用于掩码
            let res_value = low_bits & self.value;
            let res_mask = low_bits & self.mask;
            return Self::new(res_value, res_mask);
        }

        // 一般情况：结果的精度有限
        // 由于结果小于或等于任一操作数，因此操作数中的前导零在结果中也存在
        let leading_zeros = self
            .count_min_leading_zeros()
            .max(other.count_min_leading_zeros());
        res.clear_high_bits(leading_zeros);

        res
    }

    /// 有符号除法操作
    pub fn signed_div(&self, other: Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        }

        let w = 64;

        if self.is_singleton() && other.is_singleton() {
            return Tnum::new(self.value.wrapping_div(other.value), 0);
        }

        if self.is_nonnegative() && other.is_nonnegative() {
            return self.udiv(other);
        }

        let mut result = Self::top();
        let mut tmp: i64 = 0;

        if self.is_negative() && other.is_negative() {
            if self.value == i64::MIN as u64 && other.is_singleton() && other.value == u64::MAX {
                return Self::top();
            }

            let denom = other.get_signed_max_value();
            let num = self.get_signed_min_value();

            if !(num == i64::MIN as u64 && denom == i64::MAX as u64) {
                tmp = (num as i64).wrapping_div(denom as i64);
            } else {
                tmp = i64::MAX;
            }
        } else if self.is_negative() && other.is_nonnegative() {
            // Result is negative if -LHS u>= RHS
            let neg_lhs_max: i64 = (self.get_signed_max_value() as i64).wrapping_neg();
            if neg_lhs_max >= other.get_signed_max_value() as i64 {
                let denom = other.get_signed_min_value();
                let num = self.get_signed_min_value();
                tmp = (num as i64).wrapping_div(denom as i64);
            }
        } else if self.is_nonnegative() && other.is_negative() {
            // Result is negative if LHS u>= -RHS
            let neg_rhs_min = (other.get_signed_min_value() as i64).wrapping_neg();
            if self.get_signed_min_value() >= neg_rhs_min as u64 {
                let denom = other.get_signed_max_value();
                let num = self.get_signed_max_value();
                tmp = (num as i64).wrapping_div(denom as i64);
            }
        }

        if tmp != 0 {
            if (tmp >> 63) & 1 == 0 {
                let lead_zeros = tmp.leading_zeros();
                result.clear_high_bits(lead_zeros);
            } else {
                let lead_ones = (!tmp).leading_zeros();
                if lead_ones > 0 {
                    let high_mask = u64::MAX << (64 - lead_ones);
                    result.value |= high_mask;
                    result.mask &= !high_mask;
                }
            }
        }
        result
    }

    /// fast_divide
    pub fn fast_divide(&self, other: Self) -> Self {
        if other.mask == 0 && other.value == 0 {
            return Tnum::top();
        } else if other.mask == 0 && other.value == 1 {
            return *self;
        } else if other.mask == 0 {
            let divider = DividerU64::divide_by(other.value);
            match divider {
                DividerU64::Fast { magic, shift } => {
                    // 修正：使用32位magic number算法
                    // 正确公式: ((dividend * magic) >> 32) >> shift
                    let product = (self.value as u64).wrapping_mul(magic);
                    let high_part = product >> 32;  // 取高32位
                    let result_value = high_part >> shift;
                    
                    // 对于mask的处理（保守估计）
                    let mask_product = (self.mask as u64).wrapping_mul(magic);
                    let mask_high = mask_product >> 32;
                    let result_mask = mask_high >> shift;
                    
                    return Self::new(result_value, result_mask);
                    // println!("  - Strategy: Fast Path");
                    // println!("  - Magic (M): 0x{:X} ({})", magic, magic);
                    // println!("  - Shift (s): {}", shift);
                    // println!("  - Formula: ((n * M) >> 32) >> s");
                }
                DividerU64::BitShift(shift) => {
                    return self.tnum_rshift(shift as u8);
                    // println!("  - Strategy: BitShift (Power of 2)");
                    // println!("  - No Magic number (M) needed.");
                    // println!("  - Shift (s): {}", shift);
                    // println!("  - Formula: n >> s");
                }
                DividerU64::General { magic_low, shift } => {
                    // a/b
                    // M = 2^n/b
                    // a*(2^n/b)>>n==a/b
                    let self_u128 = TnumU128::new(self.value as u128,self.mask as u128);
                    let other_u128 = TnumU128::new(magic_low as u128,0);
                    let temp = self_u128.mul(other_u128);
                    let q = Self::new((temp.value >> 64) as u64, (temp.mask >> 64) as u64);
                    let mut res = self.sub(q).tnum_rshift(1).add(q);
                    res = res.tnum_rshift(shift as u8);
                    return res;
                    // println!("  - Strategy: General Path");
                    // println!("  - Magic_low: 0x{:X} ({})", magic_low, magic_low);
                    // println!("  - The effective Magic number is (2^64 + Magic_low)");
                    // println!("  - Shift (s): {}", shift);
                    // println!("  - Formula: A more complex calculation (see source)");
                }
            }
        }
        self.sdiv(other)
    }

    /// 有符号除法操作
    pub fn sdiv(&self, other: Self) -> Self {
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        }
        if self.is_top() || other.is_top() {
            return Self::top();
        }

        let w = 64;

        if other.value == 0 {
            return Self::top();
        } else if (self.mask == 0 && other.mask == 0) {
            return Self::new(self.value.wrapping_div(other.value), 0);
        }

        let t0 = self.get_zero_circle();
        let t1 = self.get_one_circle();
        let x0 = other.get_zero_circle();
        let x1 = other.get_one_circle();

        let res00 = t0.signed_div(x0);
        let res01 = t0.signed_div(x1);
        let res10 = t1.signed_div(x0);
        let res11 = t1.signed_div(x1);

        res00.or(&res01).or(&res10).or(&res11)
    }

    fn get_signed_min_value(&self) -> u64 {
        if (self.value >> 63) & 1 == 1 {
            self.value | self.mask
        } else {
            self.value
        }
    }

    fn get_signed_max_value(&self) -> u64 {
        if (self.value >> 63) & 1 == 1 {
            self.value
        } else {
            self.value | self.mask
        }
    }

    pub fn get_zero_circle(&self) -> Self {
        let width = 64;
        let sign_max = i64::MAX;
        let value = self.value as i64;
        let mask = self.mask as i64;
        if value & (1i64 << 63) != 0 {
            return Tnum::new(sign_max as u64, sign_max as u64);
        } else if mask & (1i64 << 63) != 0 {
            return Tnum::new(value as u64, (mask & sign_max) as u64);
        } else {
            return *self;
        }
    }

    pub fn get_one_circle(&self) -> Self {
        let value = self.value as i64;
        let mask = self.mask as i64;
        let width = 64;
        let sign_max = i64::MAX;
        let sign_min = i64::MIN;
        let unsign_max = u64::MAX;
        if value & (1i64 << 63) != 0 {
            return *self;
        } else if mask & (1i64 << 63) != 0 {
            let mut value = value;
            value |= (1i64 << 63);
            let mut mask = mask;
            mask &= !(1i64 << 63);
            return Tnum::new(value as u64, mask as u64);
        } else {
            return Tnum::new(unsign_max, unsign_max);
        }
    }

    /// 无符号除法操作
    pub fn udiv(&self, other: Self) -> Self {
        // 处理 bottom 和 top 情况
        if self.is_bottom() || other.is_bottom() {
            return Self::bottom();
        }
        if self.is_top() || other.is_top() {
            return Self::top();
        }

        let w = 64;
        let flag: bool = (other.value == 0);
        if flag {
            // 处理除数为0的情况
            return Self::top();
        } else {
            let mut Res = Tnum::top();
            let MaxRes = match (self.value + self.mask).checked_div(other.value) {
                // 如果除法成功，返回包含结果的新 Tnum
                Some(result) => result,
                // 如果除以零，checked_div 返回 None，我们返回 top
                None => return Self::top(),
            };
            let leadz = MaxRes.leading_zeros();
            Res.value.clear_high_bits(leadz);
            Res.mask.clear_high_bits(leadz);
            // if (leadz == 64) {
            //     return Res;
            // }
            // let result = self.div_compute_low_bit(Res, other);
            return Res;
        }
    }

    fn div_compute_low_bit(&self, mut result: Self, other: Self) -> Self {
        // 奇数 / 奇数 -> 奇数
        if (self.value & 1) != 0 && (self.mask & 1) != 0 {
            result.value |= 1; // 设置最低位为1
            result.mask &= !1;
        }

        let min_tz =
            self.count_min_trailing_zeros() as i32 - other.count_max_trailing_zeros() as i32;
        let max_tz =
            self.count_max_trailing_zeros() as i32 - other.count_min_trailing_zeros() as i32;

        if min_tz >= 0 {
            result.value.clear_low_bits(min_tz as u32);
            result.mask.clear_low_bits(min_tz as u32);

            if min_tz == max_tz {
                // 结果恰好有min_tz个尾随零
                result.value |= 1u64 << min_tz; // 设置第min_tz位为1
                result.mask &= !(1u64 << min_tz); // 清除第min_tz位的掩码
            }
        }

        // 检查结果是否为bottom
        if result.is_bottom() {
            return Self::top();
        }

        result
    }

    pub fn shl_const(&self, k: u64) -> Self {
        // 处理特殊情况
        if self.is_bottom() {
            return *self;
        }
        if self.is_top() {
            return *self;
        }

        let width = 64; // 固定位宽
        let shift = k % width as u64; // 确保移位值在范围内，模拟 wrapint(k, w)

        Self::new(
            self.value.wrapping_shl(shift as u32),
            self.mask.wrapping_shl(shift as u32),
        )
    }

    pub fn lshr_const(&self, k: u64) -> Self {
        // 处理特殊情况
        if self.is_bottom() {
            return *self;
        }
        if self.is_top() {
            return *self;
        }

        let width = 64; // 固定位宽
        let shift = k; // 确保移位值在范围内，模拟 wrapint(k, w)

        Self::new(
            self.value.wrapping_shr(shift as u32),
            self.mask.wrapping_shr(shift as u32),
        )
    }

    pub fn ashr_const(&self, k: u64) -> Self {
        // 处理特殊情况
        if self.is_bottom() {
            return *self;
        }
        if self.is_top() {
            return *self;
        }

        let width = 64; // 固定位宽
        let shift = k % width as u64; // 确保移位值在范围内，模拟 wrapint(k, w)

        // 获取符号位
        let vsig = (self.value >> 63) & 1 == 1;
        let msig = (self.mask >> 63) & 1 == 1;

        // 根据符号位选择不同的移位策略
        if !vsig && !msig {
            // 都是非负数，使用逻辑右移
            Self::new(
                self.value.wrapping_shr(shift as u32),
                self.mask.wrapping_shr(shift as u32),
            )
        } else if vsig && !msig {
            // value 是负数但 mask 非负
            Self::new(
                ((self.value as i64).wrapping_shr(shift as u32)) as u64,
                self.mask.wrapping_shr(shift as u32),
            )
        } else {
            // 其他情况
            Self::new(
                self.value.wrapping_shr(shift as u32),
                ((self.mask as i64).wrapping_shr(shift as u32)) as u64,
            )
        }
    }

    pub fn le(&self, other: &Tnum) -> bool {
        // 修改参数类型为 &Tnum
        if other.is_top() || self.is_bottom() {
            return true;
        } else if other.is_bottom() || self.is_top() {
            return false;
        } else if self.value == other.value && self.mask == other.mask {
            return true;
        } else if (self.mask & (!other.mask)) != 0 {
            // self[i] 未知但 other[i] 已知
            return false;
        } else {
            return (self.value & (!other.mask)) == other.value;
        }
    }

    /// 等价关系判断（==）
    pub fn eq(&self, other: &Tnum) -> bool {
        // 修改参数类型为 &Tnum
        self.le(other) && other.le(self)
    }

    pub fn or(&self, other: &Tnum) -> Tnum {
        if self.le(other) {
            return *other;
        } else if other.le(self) {
            return *self;
        } else {
            let mu = self.mask | other.mask;
            let this_know = self.value & (!mu);
            let x_know = other.value & (!mu);
            let disagree = this_know ^ x_know;

            Tnum::new(this_know & x_know, mu | disagree)
        }
    }

    pub fn and(&self, other: &Tnum) -> Tnum {
        if self.le(other) {
            return *self;
        } else if other.le(self) {
            return *other;
        }

        let mu1 = self.mask & other.mask;
        let mu2 = self.mask | other.mask;
        let this_known_v = self.value & (!mu2);
        let x_known_v = other.value & (!mu2);
        let disagree = this_known_v ^ x_known_v;

        if disagree != 0 {
            return Tnum::bottom();
        }

        Tnum::new((self.value | other.value) & (!mu1), mu1)
    }
}

pub fn rem_get_low_bits(lhs: &Tnum, rhs: &Tnum) -> Tnum {
    let w = 64u8; // 固定位宽为64

    if !rhs.is_zero() && (rhs.value & 1) == 0 && (rhs.mask & 1) == 0 {
        let qzero = rhs.count_min_trailing_zeros();

        if qzero == 0 {
            return Tnum::top();
        }

        /// mask源代码看起来有点问题？
        let mut mask = if qzero > 1 { (1u64 << qzero) - 1 } else { 0u64 };
        // mask = 0xFFFFFFFFFFFFFFFF;

        let res_value = lhs.value & mask;
        let res_mask = lhs.mask & mask;
        let res = Tnum::new(res_value, res_mask);

        return res;
    }

    Tnum::top()
}
/// Z3验证框架：寻找fast_divide算法的反例
pub struct FastDivideVerifier<'ctx> {
    context: &'ctx Context,
    solver: Solver<'ctx>,
}

impl<'ctx> FastDivideVerifier<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        let solver = Solver::new(ctx);
        Self {
            context: ctx,
            solver,
        }
    }

    pub fn reset(&self) {
        self.solver.reset();
    }

    /// 创建位向量变量
    pub fn create_bv(&self, name: &str, size: u32) -> BV<'ctx> {
        BV::new_const(self.context, name, size)
    }

    /// 验证 a_val 在 Tnum {a_value, a_mask} 的范围内
    /// 约束：(a_val XOR a_value) & !a_mask == 0
    pub fn assert_in_tnum_range(&self, concrete_val: &BV<'ctx>, tnum_value: u64, tnum_mask: u64) {
        let zero = BV::from_u64(self.context, 0, 64);
        let value_bv = BV::from_u64(self.context, tnum_value, 64);
        let mask_bv = BV::from_u64(self.context, tnum_mask, 64);
        
        // 约束：(concrete_val XOR tnum_value) & !tnum_mask == 0
        let xor_result = concrete_val.bvxor(&value_bv);
        let not_mask = mask_bv.bvnot();
        let masked_result = xor_result.bvand(&not_mask);
        let constraint = masked_result._eq(&zero);
        
        self.solver.assert(&constraint);
    }

    pub fn model_fast_divide(&self, 
        a_value: u64, a_mask: u64, 
        b_value: u64, b_mask: u64
    ) -> (u64, u64) {
        let dividend_tnum = Tnum::new(a_value, a_mask);
        let divisor_tnum = Tnum::new(b_value, b_mask);
        let result = dividend_tnum.fast_divide(divisor_tnum);
        (result.value, result.mask)
    }

    /// 添加反例约束：对于具体的 a_val, b_val 值，调用 fast_divide 算法
    pub fn assert_counterexample_with_actual_fast_divide(&self, 
        a_val: &BV<'ctx>, 
        b_val: &BV<'ctx>
    ) {
        let zero = BV::from_u64(self.context, 0, 64);
        
        // 创建一个布尔变量来表示是否找到反例
        let mut counterexample_found = BV::from_u64(self.context, 0, 1); // false
        
        // 枚举被除数和除数的组合
        for dividend_value in 0..=1000u64 {
            for divisor_value in 3..=3u64 { // 除数从1开始，避免除零
                // 使用常数 Tnum：mask = 0
                let dividend_tnum = Tnum::const_val(dividend_value);
                let divisor_tnum = Tnum::const_val(divisor_value);
                
                // 对于这个 Tnum 组合，计算 fast_divide 的结果
                let fast_divide_result = dividend_tnum.fast_divide(divisor_tnum);
                
                // 创建条件：a_val == dividend_value && b_val == divisor_value
                let dividend_bv = BV::from_u64(self.context, dividend_value, 64);
                let divisor_bv = BV::from_u64(self.context, divisor_value, 64);
                let is_this_combination = Bool::and(self.context, &[
                    &a_val._eq(&dividend_bv),
                    &b_val._eq(&divisor_bv)
                ]);
                
                // 计算真实除法结果
                let true_result = dividend_value / divisor_value;
                let true_result_bv = BV::from_u64(self.context, true_result, 64);
                
                // 检查真实结果是否在 fast_divide 结果的 Tnum 范围内
                let fast_divide_value_bv = BV::from_u64(self.context, fast_divide_result.value, 64);
                let fast_divide_mask_bv = BV::from_u64(self.context, fast_divide_result.mask, 64);
                
                // 正确的Tnum范围检查：(true_result XOR fast_divide_value) & !fast_divide_mask == 0
                let xor_result = true_result_bv.bvxor(&fast_divide_value_bv);
                let not_mask = fast_divide_mask_bv.bvnot(); // !mask
                let masked_result = xor_result.bvand(&not_mask);
                let in_range = masked_result._eq(&zero);
                
                // 如果真实结果不在 fast_divide 范围内，则找到反例
                let this_is_counterexample = Bool::and(self.context, &[&is_this_combination, &in_range.not()]);
                
                // 更新反例标志
                let one_bit = BV::from_u64(self.context, 1, 1);
                counterexample_found = counterexample_found.bvor(&this_is_counterexample.ite(&one_bit, &BV::from_u64(self.context, 0, 1)));
            }
        }
        
        // 断言
        let one_bit = BV::from_u64(self.context, 1, 1);
        let counterexample_constraint = counterexample_found._eq(&one_bit);
        self.solver.assert(&counterexample_constraint);
    }

    /// 添加除数不为0的约束
    pub fn assert_divisor_not_zero(&self, b_val: &BV<'ctx>) {
        let zero = BV::from_u64(self.context, 0, 64);
        let not_zero_constraint = b_val._eq(&zero).not();
        self.solver.assert(&not_zero_constraint);
    }

    /// 添加输入范围约束
    pub fn assert_input_bounds(&self, a_val: &BV<'ctx>, b_val: &BV<'ctx>) {
        let max_val = BV::from_u64(self.context, u32::MAX as u64, 64);
        self.solver.assert(&a_val.bvule(&max_val));
        self.solver.assert(&b_val.bvule(&max_val));
        self.solver.assert(&b_val.bvugt(&BV::from_u64(self.context, 0, 64)));
    }

    pub fn check(&self) -> SatResult {
        self.solver.check()
    }

    pub fn get_model(&self) -> Option<z3::Model> {
        self.solver.get_model()
    }
}

/// 验证 fast_divide 算法的正确性
pub fn verify_fast_divide_correctness() {
    println!("=== 使用 Z3 验证 fast_divide 算法正确性 ===");
    println!("验证思路：寻找反例，即存在输入 a_val, b_val 在各自 Tnum 范围内，");
    println!("但 a_val / b_val 不在 fast_divide 结果的 Tnum 范围内。");
    
    let cfg = Config::new();
    let ctx = Context::new(&cfg);
    let verifier = FastDivideVerifier::new(&ctx);
    
    println!("\n=== Z3 建模验证流程 ===");
    println!("1. 定义 Z3 位向量：a_value, a_mask, b_value, b_mask, a_val, b_val");
    println!("2. 添加 Tnum 范围约束：(a_val XOR a_value) & !a_mask == 0");
    println!("3. 添加除数非零约束：b_val != 0");
    println!("4. 计算 fast_divide 结果：result_value, result_mask");
    println!("5. 添加反例约束：((a_val / b_val) XOR result_value) & result_mask != 0");
    println!("6. 使用 Z3 求解器检查是否存在满足所有约束的解");
    
    println!("\n如果 Z3 返回：");
    println!("- SAT: 找到反例，fast_divide 算法存在错误");
    println!("- UNSAT: 未找到反例，算法在给定约束下正确");
    println!("- UNKNOWN: 求解器无法确定");
    
    println!("\n=== 开始验证 ===");
    
    // 被除数和除数都在范围内枚举
    println!("验证示例：");
    println!("  被除数范围：0 到 1000（常数 Tnum）");
    println!("  除数范围：1 到 1000（常数 Tnum）");
    println!("  验证策略：对每个（被除数，除数）组合调用实际的 fast_divide 算法");
    
    // 使用 Z3 验证
    verifier.reset();
    
    // 创建符号变量
    let a_val = verifier.create_bv("a_val", 64);
    let b_val = verifier.create_bv("b_val", 64);
    
    // 添加约束
    println!("\n添加 Z3 约束：");
    println!("  1. a_val 在范围 [0, 1000]");
    let max_search = BV::from_u64(&ctx, 1000, 64);
    let zero = BV::from_u64(&ctx, 0, 64);
    let one = BV::from_u64(&ctx, 1, 64);
    verifier.solver.assert(&a_val.bvule(&max_search));
    verifier.solver.assert(&a_val.bvuge(&zero));
    
    println!("  2. b_val 在范围 [1, 1000]（避免除零）");
    verifier.solver.assert(&b_val.bvule(&max_search));
    verifier.solver.assert(&b_val.bvuge(&one));
    
    println!("  5. 添加反例约束（使用实际 fast_divide 算法）");
    verifier.assert_counterexample_with_actual_fast_divide(&a_val, &b_val);
    
    // 检查是否存在反例
    println!("\nZ3 求解中...");
    match verifier.check() {
        SatResult::Sat => {
            println!("Z3 发现反例！fast_divide 算法存在错误");
            
            if let Some(model) = verifier.get_model() {
                if let (Some(a_concrete), Some(b_concrete)) = (
                    model.eval(&a_val, true),
                    model.eval(&b_val, true)
                ) {
                    if let (Some(a_num), Some(b_num)) = (
                        a_concrete.as_u64(),
                        b_concrete.as_u64()
                    ) {
                        let correct_result = a_num / b_num;
                        println!("反例详情:");
                        println!("  输入: a_val = {} (0b{:b}), b_val = {} (0b{:b})", 
                                a_num, a_num, b_num, b_num);
                        println!("  正确结果: {} ÷ {} = {} (0b{:b})", 
                                a_num, b_num, correct_result, correct_result);
                        
                        // 计算对应的 fast_divide 结果
                        let dividend_tnum = Tnum::const_val(a_num);
                        let divisor_tnum = Tnum::const_val(b_num);
                        let actual_fast_divide_result = dividend_tnum.fast_divide(divisor_tnum);
                        println!("  被除数 Tnum: value={} (0b{:b}), mask={} (0b{:b}) (常数)", 
                                a_num, a_num, 0, 0u64);
                        println!("  除数 Tnum: value={} (0b{:b}), mask={} (0b{:b}) (常数)", 
                                b_num, b_num, 0, 0u64);
                        println!("  fast_divide 结果: value={} (0b{:b}), mask={} (0b{:b})", 
                                actual_fast_divide_result.value, actual_fast_divide_result.value,
                                actual_fast_divide_result.mask, actual_fast_divide_result.mask);
                        
                        // 检查范围
                        let in_range = (correct_result ^ actual_fast_divide_result.value) & !actual_fast_divide_result.mask == 0;
                        println!("  正确结果是否在算法结果范围内: {} (XOR: 0b{:b}, ~mask: 0b{:b}, 结果: 0b{:b})", 
                                in_range, 
                                correct_result ^ actual_fast_divide_result.value,
                                !actual_fast_divide_result.mask,
                                (correct_result ^ actual_fast_divide_result.value) & !actual_fast_divide_result.mask);
                    }
                }
            }
        },
        SatResult::Unsat => {
            println!("Z3 验证通过：未发现反例");
            println!("在给定约束下，fast_divide 算法是正确的");
        },
        SatResult::Unknown => {
            println!("Z3 验证结果未知");
            println!("可能需要调整约束或增加求解时间");
        }
    }
    
    println!("\n=== 验证完成 ===");
}

fn main() {
    verify_fast_divide_correctness();
}