use rand::{RngExt, rngs::ThreadRng};
use rand_distr::{Distribution, Normal, weighted::WeightedIndex};
use smallvec::SmallVec;
use std::{
    cmp::{max, min},
    io::Write,
    ops::RangeInclusive,
};

#[path = "generator/keys.rs"]
mod keys;
#[path = "generator/lorem.rs"]
mod lorem;

macro_rules! pct_value_check {
    ($val:ident) => {
        if $val < 0.0 || $val > 1.0 {
            panic!(
                concat!(
                    stringify!($val),
                    " must be between 0.0 and 1.0, but it is {}"
                ),
                $val
            );
        }
    };
}

macro_rules! pct_group_check {
    ($($val:ident),+ ; $last:ident) => {
        {
            let mut tot = 0.0;
            $(
                pct_value_check!($val);
                tot += $val;
            )+
            pct_value_check!($last);
            tot += $last;
            if tot != 1.0 {
                panic!(concat!($(stringify!($val), ", "),+, "and ", stringify!($last), " must sum to 1.0, but their actual sum is {}"), tot)
            }
        }
    }
}

macro_rules! pct_partial_group_check {
    ($($val:ident),+ ; $last:ident) => {
        {
            let mut tot = 0.0;
            $(
                pct_value_check!($val);
                tot += $val;
            )+
            pct_value_check!($last);
            tot += $last;
            if tot > 1.0 {
                panic!(concat!($(stringify!($val), ", "),+, "and ", stringify!($last), " must sum to a value that is <= 1.0, but their actual sum is {}"), tot)
            }
        }
    }
}

pub struct ArrRules<D: Distribution<f64> = Normal<f64>> {
    len_distr: D,
}

impl<D: Distribution<f64>> ArrRules<D> {
    pub fn new(len_distr: D) -> Self {
        Self { len_distr }
    }
}

impl Default for ArrRules<Normal<f64>> {
    fn default() -> Self {
        Self::new(Normal::new(20.0, 100_000.0).unwrap())
    }
}

pub struct NumRules<D: Distribution<f64> = Normal<f64>> {
    len_distr: D,
    pct_neg: f64,
    pct_zero: f64,
    pct_frac: f64,
    pct_exp: f64,
}

impl<D: Distribution<f64>> NumRules<D> {
    pub fn new(len_distr: D, pct_neg: f64, pct_zero: f64, pct_frac: f64, pct_exp: f64) -> Self {
        pct_partial_group_check!(pct_neg; pct_zero);
        pct_partial_group_check!(pct_frac; pct_exp);

        Self {
            len_distr,
            pct_neg,
            pct_zero,
            pct_frac,
            pct_exp,
        }
    }
}

impl Default for NumRules<Normal<f64>> {
    fn default() -> Self {
        Self::new(Normal::new(5.0, 15.0).unwrap(), 0.15, 0.20, 0.25, 0.1)
    }
}

pub struct ObjRules<D: Distribution<f64>> {
    len_distr: D,
}

impl<D: Distribution<f64>> ObjRules<D> {
    pub fn new(len_distr: D) -> Self {
        Self { len_distr }
    }
}

impl Default for ObjRules<Normal<f64>> {
    fn default() -> Self {
        Self::new(Normal::new(100.0, 200_000.0).unwrap())
    }
}

#[derive(Debug, Default)]
pub enum Root {
    Arr,
    Str,
    Num,

    #[default]
    Obj,
}

pub struct StrRules<K: Distribution<f64> = Normal<f64>, V: Distribution<f64> = Normal<f64>> {
    key_len_distr: K,
    val_len_distr: V,
    pct_multiline: f64,
    pct_escaped: f64,
    pct_multibyte: f64,
}

impl<K: Distribution<f64>, V: Distribution<f64>> StrRules<K, V> {
    pub fn new(
        key_len_distr: K,
        val_len_distr: V,
        pct_multiline: f64,
        pct_escaped: f64,
        pct_multibyte: f64,
    ) -> Self {
        pct_value_check!(pct_multiline);
        pct_partial_group_check!(pct_escaped; pct_multibyte);

        Self {
            key_len_distr,
            val_len_distr,
            pct_multiline,
            pct_escaped,
            pct_multibyte,
        }
    }
}

impl Default for StrRules<Normal<f64>> {
    fn default() -> Self {
        Self::new(
            Normal::new(10.0, 10.0).unwrap(),
            Normal::new(20.0, 1_000.0).unwrap(),
            0.1,
            0.05,
            0.05,
        )
    }
}

pub struct ValueDist {
    pct_arr: f64,
    pct_lit: f64,
    pct_num: f64,
    pct_obj: f64,
    pct_str: f64,
}

impl ValueDist {
    pub fn new(pct_arr: f64, pct_lit: f64, pct_num: f64, pct_obj: f64, pct_str: f64) -> Self {
        pct_group_check!(pct_arr, pct_lit, pct_num, pct_obj; pct_str);

        Self {
            pct_arr,
            pct_lit,
            pct_num,
            pct_obj,
            pct_str,
        }
    }
}

impl Default for ValueDist {
    fn default() -> Self {
        Self::new(0.10, 0.15, 0.15, 0.15, 0.45)
    }
}

#[derive(Debug, Default)]
pub enum LineSep {
    #[default]
    N,
    R,
    Rn,
}

impl LineSep {
    fn as_bytes(&self) -> &'static [u8] {
        match self {
            Self::N => &b"\n"[..],
            Self::R => &b"\r"[..],
            Self::Rn => &b"\r\n"[..],
        }
    }
}

#[derive(Debug, Default)]
pub enum WhiteRules {
    #[default]
    Off,
    Pretty {
        line_break: LineSep,
        inline_space: u8,
        indent: usize,
    },
}

impl WhiteRules {
    pub fn off() -> Self {
        Self::Off
    }

    pub fn pretty(line_break: LineSep, inline_space: u8, indent: usize) -> Self {
        Self::Pretty {
            line_break,
            inline_space,
            indent,
        }
    }

    fn line_break(&self) -> &'static [u8] {
        match self {
            Self::Off => &b""[..],
            Self::Pretty { line_break, .. } => line_break.as_bytes(),
        }
    }

    fn inline_space(&self) -> Option<u8> {
        match self {
            Self::Off => None,
            Self::Pretty { inline_space, .. } => Some(*inline_space),
        }
    }

    fn indent(&self) -> usize {
        match self {
            Self::Off => 0,
            Self::Pretty { indent, .. } => *indent,
        }
    }
}

pub struct Generator<
    R: RngExt,
    DArr: Distribution<f64> = Normal<f64>,
    DNum: Distribution<f64> = Normal<f64>,
    DObj: Distribution<f64> = Normal<f64>,
    DStr: Distribution<f64> = Normal<f64>,
> {
    arr_rules: ArrRules<DArr>,
    max_level: usize,
    num_rules: NumRules<DNum>,
    obj_rules: ObjRules<DObj>,
    rng: R,
    root: Root,
    str_rules: StrRules<DStr>,
    value_dist: ValueDist,
    white_rules: WhiteRules,
}

impl<
    R: RngExt,
    DArr: Distribution<f64>,
    DNum: Distribution<f64>,
    DObj: Distribution<f64>,
    DStr: Distribution<f64>,
> Generator<R, DArr, DNum, DObj, DStr>
{
    pub fn with_arr_rules<DArr2: Distribution<f64>>(
        self,
        arr_rules: ArrRules<DArr2>,
    ) -> Generator<R, DArr2, DNum, DObj, DStr> {
        Generator {
            arr_rules,
            max_level: self.max_level,
            num_rules: self.num_rules,
            obj_rules: self.obj_rules,
            rng: self.rng,
            root: self.root,
            str_rules: self.str_rules,
            value_dist: self.value_dist,
            white_rules: self.white_rules,
        }
    }

    pub fn with_max_level(self, max_level: usize) -> Self {
        Self { max_level, ..self }
    }

    pub fn with_num_rules<DNum2: Distribution<f64>>(
        self,
        num_rules: NumRules<DNum2>,
    ) -> Generator<R, DArr, DNum2, DObj, DStr> {
        Generator {
            arr_rules: self.arr_rules,
            max_level: self.max_level,
            num_rules,
            obj_rules: self.obj_rules,
            rng: self.rng,
            root: self.root,
            str_rules: self.str_rules,
            value_dist: self.value_dist,
            white_rules: self.white_rules,
        }
    }

    pub fn with_obj_rules<DObj2: Distribution<f64>>(
        self,
        obj_rules: ObjRules<DObj2>,
    ) -> Generator<R, DArr, DNum, DObj2, DStr> {
        Generator {
            arr_rules: self.arr_rules,
            max_level: self.max_level,
            num_rules: self.num_rules,
            obj_rules,
            rng: self.rng,
            root: self.root,
            str_rules: self.str_rules,
            value_dist: self.value_dist,
            white_rules: self.white_rules,
        }
    }

    pub fn with_rng<R2: RngExt>(self, rng: R2) -> Generator<R2, DArr, DNum, DObj, DStr> {
        Generator {
            arr_rules: self.arr_rules,
            max_level: self.max_level,
            num_rules: self.num_rules,
            obj_rules: self.obj_rules,
            rng,
            root: self.root,
            str_rules: self.str_rules,
            value_dist: self.value_dist,
            white_rules: self.white_rules,
        }
    }

    pub fn with_root(self, root: Root) -> Self {
        Self { root, ..self }
    }

    pub fn with_str_rules<DStr2: Distribution<f64>>(
        self,
        str_rules: StrRules<DStr2>,
    ) -> Generator<R, DArr, DNum, DObj, DStr2> {
        Generator {
            arr_rules: self.arr_rules,
            max_level: self.max_level,
            num_rules: self.num_rules,
            obj_rules: self.obj_rules,
            rng: self.rng,
            root: self.root,
            str_rules,
            value_dist: self.value_dist,
            white_rules: self.white_rules,
        }
    }

    pub fn with_value_dist(self, value_dist: ValueDist) -> Self {
        Self { value_dist, ..self }
    }

    pub fn with_white_rules(self, white_rules: WhiteRules) -> Self {
        Self {
            white_rules,
            ..self
        }
    }

    pub fn generate(&mut self, len: usize, w: &mut impl Write) -> std::io::Result<usize> {
        let insufficient_len = |root: Root, min_len: usize| {
            panic!(
                "root {root:?} requires at least {min_len} bytes, but only {len} were requested"
            );
        };

        let mut seps = Seps::new(&self.white_rules);

        match self.root {
            Root::Arr if len >= 2 => self.generate_arr(len..=len, 0, &mut seps, w),
            Root::Arr => insufficient_len(Root::Arr, 2),
            Root::Str if len >= 2 => self.generate_str(len..=len, false, w),
            Root::Str => insufficient_len(Root::Str, 2),
            Root::Num if len >= 1 => self.generate_num(len..=len, w),
            Root::Num => insufficient_len(Root::Num, 1),
            Root::Obj if len >= 2 => self.generate_obj(len..=len, 0, &mut seps, w),
            Root::Obj => insufficient_len(Root::Obj, 2),
        }
    }

    fn generate_arr(
        &mut self,
        rng: RangeInclusive<usize>,
        level: usize,
        seps: &mut Seps,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        assert!(
            *rng.start() >= 2,
            "array requires at least 2 bytes (for the opening and closing brackets), but the requested range is {rng:?}"
        );

        let len = if rng.start() < rng.end() {
            self.arr_rules
                .len_distr
                .sample(&mut self.rng)
                .clamp(*rng.start() as f64, *rng.end() as f64) as usize
        } else {
            *rng.start()
        };

        let inner_len = len - 2;
        let struct_sep_len = 2 * seps.struct_sep.len() + seps.indent;

        w.write_all(b"[")?;
        if inner_len >= struct_sep_len {
            seps.push_level();
            w.write_all(&seps.struct_sep)?;
            self.generate_arr_items(inner_len - struct_sep_len, level + 1, seps, w)?;
            seps.pop_level();
            w.write_all(&seps.struct_sep)?;
        } else {
            self.generate_arr_items(inner_len, self.max_level, seps, w)?;
        };
        w.write_all(b"]")?;

        Ok(len)
    }

    fn generate_arr_items(
        &mut self,
        len: usize,
        level: usize,
        seps: &mut Seps,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        const MIN_ITEM: usize = 1; // Smallest possible array item is a number of length 1.
        if level <= self.max_level && len >= MIN_ITEM {
            let mut n = 0;

            loop {
                let m = if len - n >= 2 * MIN_ITEM + seps.val_sep.len() {
                    let max_item = len - n - MIN_ITEM - seps.val_sep.len();

                    self.generate_val(MIN_ITEM..=max_item, level, seps, w)?
                } else {
                    self.generate_val(len - n..=len - n, level, seps, w)?
                };

                n += m;
                if n == len {
                    return Ok(len);
                }

                assert!(len - n >= MIN_ITEM + seps.val_sep.len());

                w.write_all(&seps.val_sep)?;
                n += seps.val_sep.len();

                assert!(len - n >= MIN_ITEM);
            }
        } else {
            Self::generate_white_spaces(len, w)
        }
    }

    fn generate_lit(
        &mut self,
        rng: RangeInclusive<usize>,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        assert!(
            *rng.end() >= 4 && *rng.start() <= 5,
            "literals are 4-5, but range given is {rng:?}"
        );
        assert!(rng.start() <= rng.end());

        let lit = match (rng.start(), rng.end()) {
            (..=4, 4) => ["null", "true"][self.rng.random_range(0..=1)],
            (..=4, 5..) => ["null", "true", "false"][self.rng.random_range(0..=2)],
            (5, 5) => "false",
            _ => unreachable!(),
        };

        w.write_all(lit.as_bytes())?;

        Ok(lit.len())
    }

    fn generate_num(
        &mut self,
        mut rng: RangeInclusive<usize>,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        assert!(
            *rng.start() >= 1,
            "number requires at least 1 byte, but the requested range is {rng:?}"
        );
        assert!(rng.start() <= rng.end());

        if *rng.start() == 1 && self.rng.random_bool(self.num_rules.pct_zero) {
            w.write_all(&[b'0'])?;

            return Ok(1);
        } else if *rng.end() == 1 {
            return self.generate_int(1, false, w);
        }

        let sign_len = if *rng.start() > 1 && self.rng.random_bool(self.num_rules.pct_neg) {
            w.write_all(&[b'-'])?;
            rng = *rng.start() - 1..=*rng.end() - 1;

            1
        } else {
            0
        };

        if *rng.end() < 3 {
            let len = self.rng.random_range(rng);
            self.generate_int(len, true, w)?;

            return Ok(sign_len + len);
        }

        let min_frac = if self.rng.random_bool(self.num_rules.pct_frac) {
            2
        } else {
            0
        };
        let min_exp = if rng.end().saturating_sub(min_frac) >= 4
            && self.rng.random_bool(self.num_rules.pct_exp)
        {
            3
        } else {
            0
        };

        let mut len = self
            .num_rules
            .len_distr
            .sample(&mut self.rng)
            .clamp(*rng.start() as f64, *rng.end() as f64) as usize;
        if len.saturating_sub(min_frac + min_exp) < 1 {
            len = 1 + min_frac + min_exp;
        }
        assert!(rng.contains(&len));

        let int_len = if min_frac == 0 && min_exp == 0 {
            len
        } else {
            self.num_rules
                .len_distr
                .sample(&mut self.rng)
                .clamp(1.0, (len - min_frac - min_exp) as f64) as usize
        };

        let frac_len = if min_frac == 0 {
            0
        } else if min_exp == 0 {
            len - int_len
        } else {
            self.num_rules
                .len_distr
                .sample(&mut self.rng)
                .clamp(min_frac as f64, (len - int_len - min_exp) as f64) as usize
        };

        let exp_len = len - int_len - frac_len;

        self.generate_int(int_len, false, w)?;
        if frac_len > 0 {
            w.write_all(&[b'.'])?;
            self.generate_int(frac_len - 1, true, w)?;
        }
        if exp_len > 0 {
            let prefix = &[
                if self.rng.random_bool(0.5) {
                    b'e'
                } else {
                    b'E'
                },
                if self.rng.random_bool(0.5) {
                    b'-'
                } else {
                    b'+'
                },
            ];
            w.write_all(prefix)?;
            self.generate_int(exp_len - 2, true, w)?;
        }

        Ok(sign_len + len)
    }

    fn generate_int(
        &mut self,
        len: usize,
        allow_leading_zero: bool,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        assert!(len >= 1);

        let min_digit = if len == 1 || allow_leading_zero {
            b'0'
        } else {
            b'1'
        };
        let digit = self.rng.random_range(min_digit..=b'9');
        w.write_all(&[digit])?;

        for _ in 2..=len {
            let digit = self.rng.random_range(b'0'..=b'9');
            w.write_all(&[digit])?;
        }

        Ok(len)
    }

    fn generate_obj(
        &mut self,
        rng: RangeInclusive<usize>,
        level: usize,
        seps: &mut Seps,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        assert!(
            *rng.start() >= 2,
            "object requires at least 2 bytes (for the opening and closing braces), but the requested range is {rng:?}"
        );

        let len = if rng.start() < rng.end() {
            self.obj_rules
                .len_distr
                .sample(&mut self.rng)
                .clamp(*rng.start() as f64, *rng.end() as f64) as usize
        } else {
            *rng.start()
        };

        let inner_len = len - 2;
        let struct_sep_len = 2 * seps.struct_sep.len() + seps.indent;

        w.write_all(b"{")?;
        if inner_len >= struct_sep_len {
            seps.push_level();
            w.write_all(&seps.struct_sep)?;
            self.generate_obj_members(inner_len - struct_sep_len, level + 1, seps, w)?;
            seps.pop_level();
            w.write_all(&seps.struct_sep)?;
        } else {
            self.generate_obj_members(inner_len, self.max_level, seps, w)?;
        };
        w.write_all(b"}")?;

        Ok(len)
    }

    fn generate_obj_members(
        &mut self,
        len: usize,
        level: usize,
        seps: &mut Seps,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        let min_member = self.min_len_obj_member();
        if level <= self.max_level && len >= min_member {
            let mut n = 0;

            loop {
                let m = if len - n >= 2 * min_member + seps.val_sep.len() {
                    let max_member = len - n - min_member - seps.val_sep.len();

                    self.generate_obj_member(min_member..=max_member, level, seps, w)?
                } else {
                    self.generate_obj_member(len - n..=len - n, level, seps, w)?
                };

                n += m;
                if n == len {
                    return Ok(len);
                }

                assert!(
                    len - n >= seps.val_sep.len() + min_member,
                    "need enough space for the separator ({}) + a member ({min_member}), but only {} bytes remain (len={len}, n={n}, m={m})",
                    seps.val_sep.len(),
                    len - n
                );

                w.write_all(&seps.val_sep)?;
                n += seps.val_sep.len();

                assert!(len - n >= min_member);
            }
        } else {
            Self::generate_white_spaces(len, w)
        }
    }

    fn generate_obj_member(
        &mut self,
        rng: RangeInclusive<usize>,
        level: usize,
        seps: &mut Seps,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        assert!(*rng.start() >= self.min_len_obj_member());
        assert!(rng.start() <= rng.end());

        let mut name_sep_buf = [b':', 0u8];
        let name_sep = match self.white_rules.inline_space() {
            None => &name_sep_buf[..1],
            Some(b) => {
                name_sep_buf[1] = b;

                &name_sep_buf[..]
            }
        };

        let key_rng = 2..=(*rng.end() - name_sep.len() - 1); // 1 byte for colon, maybe 1 byte for name separator, at least 1 for value.
        let key_len = self.generate_str(key_rng, true, w)?;
        w.write_all(name_sep)?;
        let used_len = key_len + name_sep.len();
        let val_min_len = if used_len >= *rng.start() {
            1
        } else {
            rng.start() - used_len
        };
        let val_max_len = rng.end() - key_len - name_sep.len();
        let val_len = self.generate_val(val_min_len..=val_max_len, level, seps, w)?;
        let len = key_len + name_sep.len() + val_len;

        assert!(
            rng.contains(&len),
            "member length must fit in range {rng:?}, but {len} does not (key_len={key_len}, name_sep.len()={}, val_len={val_len})",
            name_sep.len()
        );

        Ok(len)
    }

    fn generate_str(
        &mut self,
        rng: RangeInclusive<usize>,
        is_key: bool,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        assert!(*rng.start() >= 2);
        assert!(rng.start() <= rng.end());

        w.write_all(&[b'"'])?;

        let len_sample = if is_key {
            self.str_rules.key_len_distr.sample(&mut self.rng)
        } else {
            self.str_rules.val_len_distr.sample(&mut self.rng)
        };

        let len = len_sample.clamp(*rng.start() as f64, *rng.end() as f64) as usize;

        if is_key && len - 2 < keys::KEYS.len() {
            let key_options = keys::KEYS[len - 2];
            let key = key_options[self.rng.random_range(0..key_options.len())];
            assert_eq!(len - 2, key.len());
            w.write_all(key.as_bytes())?;
        } else if self.rng.random_bool(self.str_rules.pct_multiline) {
            self.generate_str_multiline(len - 2, w)?;
        } else {
            let mut lorem_cursor = self.lorem_cursor();

            self.generate_str_line(len - 2, &mut lorem_cursor, w)?;
        }

        w.write_all(&[b'"'])?;

        Ok(len)
    }

    fn generate_str_multiline(&mut self, len: usize, w: &mut impl Write) -> std::io::Result<usize> {
        let term = if self.rng.random_bool(0.95) {
            &b"\\n"[..]
        } else if self.rng.random_bool(0.75) {
            &b"\\r\\n"[..]
        } else {
            &b"\\r"[..]
        };

        let mut lorem_cursor = self.lorem_cursor();
        let mut rem = len;

        while rem >= term.len() {
            let line_len = self
                .str_rules
                .val_len_distr
                .sample(&mut self.rng)
                .clamp(0.0, (rem - term.len()) as f64) as usize;
            self.generate_str_line(line_len, &mut lorem_cursor, w)?;
            w.write_all(term)?;
            rem -= line_len;
            rem -= term.len();
        }

        if rem > 0 {
            self.generate_str_line(rem, &mut lorem_cursor, w)?;
        }

        Ok(len)
    }

    fn generate_str_line(
        &mut self,
        len: usize,
        lorem_cursor: &mut Option<usize>,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        let mut rem = len;

        while rem > 0 {
            // Multibyte character.
            if rem >= 2 && self.rng.random_bool(self.str_rules.pct_multibyte) {
                let c = match rem {
                    2..=3 => CharRange::random_char_byte_range(2..=rem, &mut self.rng),
                    4.. => CharRange::random_char_byte_range(2..=4, &mut self.rng),
                    _ => unreachable!(),
                };

                let mut buf = [0u8; 4];
                let b = c.encode_utf8(&mut buf).as_bytes();
                assert!(
                    b.len() <= rem,
                    "encoded UTF-8 bytes ({b:?}) must fit in remaining length ({rem})"
                );

                w.write_all(b)?;

                rem -= b.len();

                continue;
            }

            // Escape sequence.
            if rem >= 6 && self.rng.random_bool(self.str_rules.pct_escaped) {
                let c = match rem {
                    6..=11 => CharRange::random_char_byte_range(1..=3, &mut self.rng),
                    12.. => CharRange::random_char_byte_range(1..=4, &mut self.rng),
                    _ => unreachable!(),
                };

                let mut unit_buf = [0u16; 2];
                let units = c.encode_utf16(&mut unit_buf);
                assert!(6 * units.len() <= rem);

                let mut byte_buf = [
                    b'\\', b'u', 0u8, 0u8, 0u8, 0u8, b'\\', b'u', 0u8, 0u8, 0u8, 0u8,
                ];

                fn encode_unit(b: &mut [u8], c: u16, lc: bool) {
                    let hex = if lc {
                        b"0123456789abcdef"
                    } else {
                        b"0123456789ABCDEF"
                    };
                    b[0] = hex[(c >> 12) as usize];
                    b[1] = hex[(c >> 8 & 0xF) as usize];
                    b[2] = hex[(c >> 4 & 0xF) as usize];
                    b[3] = hex[(c & 0xF) as usize];
                }

                let lc = self.rng.random_bool(0.75);

                encode_unit(&mut byte_buf[2..6], units[0], lc);
                if units.len() == 1 {
                    w.write_all(&byte_buf[0..6])?;
                    rem -= 6;
                } else {
                    encode_unit(&mut byte_buf[8..], units[1], lc);
                    w.write_all(&byte_buf[..])?;
                    rem -= 12;
                }

                continue;
            }

            // Trusted lorem ipsum text.
            if let Some(mut i) = *lorem_cursor {
                let j = min(i + rem, lorem::LOREM.len());
                w.write_all(&lorem::LOREM[i..j])?;
                rem -= j - i;
                i = j;
                if i < lorem::LOREM.len() {
                    *lorem_cursor = Some(i);
                } else {
                    *lorem_cursor = Some(0);
                }

                continue;
            }

            // Ordinary single-byte character (some must be escaped using '\').
            let b = match self.rng.random_range(b' '..=0x7f) {
                b'\x08' | b'\t' | b'\n' | b'\x0c' | b'\r' | b'"' | b'\\' if rem == 1 => &b" "[..],
                b'\x08' => &br#"\b"#[..],
                b'\t' => &br#"\t"#[..],
                b'\n' => &br#"\n"#[..],
                b'\x0c' => &br#"\f"#[..],
                b'\r' => &br#"\r"#[..],
                b'"' => &br#"\""#[..],
                b'\\' => &br#"\\"#[..],
                printable => &[printable],
            };

            assert!(
                rem >= b.len(),
                "can't write more bytes ({} => {b:?}) than space remaining {rem}",
                b.len()
            );

            w.write_all(b)?;
            rem -= b.len();
        }

        Ok(len)
    }

    fn lorem_cursor(&mut self) -> Option<usize> {
        if self.rng.random_bool(0.90) {
            let start = lorem::LOREM[..=self.rng.random_range(0..lorem::LOREM.len())]
                .iter()
                .rposition(|&b| b != b' ')
                .unwrap_or(0);

            Some(start)
        } else {
            None
        }
    }

    fn generate_val(
        &mut self,
        rng: RangeInclusive<usize>,
        level: usize,
        seps: &mut Seps,
        w: &mut impl Write,
    ) -> std::io::Result<usize> {
        assert!(
            *rng.end() >= 1,
            "minimum value size is 1 (for a number), but range given is {rng:?}"
        );
        assert!(rng.start() <= rng.end());

        let (hat, weights) = self.generate_val_setup(rng.clone());
        let dist = WeightedIndex::new(&weights).unwrap();
        let drawn = hat[dist.sample(&mut self.rng)];

        let len = match drawn {
            ValueKind::Arr => {
                self.generate_arr(max(2, *rng.start())..=*rng.end(), level, seps, w)?
            }
            ValueKind::Lit => self.generate_lit(max(4, *rng.start())..=*rng.end(), w)?,
            ValueKind::Num => self.generate_num(rng.clone(), w)?,
            ValueKind::Obj => {
                self.generate_obj(max(2, *rng.start())..=*rng.end(), level, seps, w)?
            }
            ValueKind::Str => self.generate_str(max(2, *rng.start())..=*rng.end(), false, w)?,
        };

        assert!(
            rng.contains(&len),
            "value length must fit in {rng:?}, but length {len} of {drawn:?} does not"
        );

        Ok(len)
    }

    fn generate_val_setup(
        &mut self,
        rng: RangeInclusive<usize>,
    ) -> (SmallVec<[ValueKind; 5]>, SmallVec<[f64; 5]>) {
        assert!(rng.start() <= rng.end());

        let mut hat = SmallVec::<[ValueKind; 5]>::new();
        let mut weights = SmallVec::<[f64; 5]>::new();

        // Since the maximum length is always at least 1, a number is always possible.
        hat.push(ValueKind::Num);
        weights.push(self.value_dist.pct_num);

        // If the maximum length is at least 2, arrays, objects, and strings are also possible.
        if *rng.end() < 2 {
            return (hat, weights);
        }
        hat.push(ValueKind::Arr);
        weights.push(self.value_dist.pct_arr);
        hat.push(ValueKind::Obj);
        weights.push(self.value_dist.pct_obj);
        hat.push(ValueKind::Str);
        weights.push(self.value_dist.pct_str);

        // If the maximum length is at least 4 (length of `null` and `true`) and the minimum length
        // is at most 5 (length of `false`), a literal is possible.
        if *rng.end() < 4 || *rng.start() > 5 {
            return (hat, weights);
        }
        hat.push(ValueKind::Lit);
        weights.push(self.value_dist.pct_lit);

        (hat, weights)
    }

    fn generate_white_spaces(len: usize, w: &mut impl Write) -> std::io::Result<usize> {
        let buf = [b' '; 16];
        let mut rem = len;

        while rem > buf.len() {
            w.write_all(&buf[..])?;
            rem -= buf.len();
        }

        if rem > 0 {
            w.write_all(&buf[..rem])?;
        }

        Ok(len)
    }

    fn min_len_obj_member(&self) -> usize {
        if matches!(self.white_rules, WhiteRules::Off) {
            4 // "a":1
        } else {
            5 // "a": 1
        }
    }
}

impl Default for Generator<ThreadRng, Normal<f64>, Normal<f64>, Normal<f64>, Normal<f64>> {
    fn default() -> Self {
        Self {
            arr_rules: ArrRules::default(),
            max_level: 1000,
            num_rules: NumRules::default(),
            obj_rules: ObjRules::default(),
            rng: ThreadRng::default(),
            root: Root::default(),
            str_rules: StrRules::default(),
            value_dist: ValueDist::default(),
            white_rules: WhiteRules::default(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
enum ValueKind {
    Arr,
    Lit,
    Num,
    Obj,
    Str,
}

#[derive(Clone, Copy, Debug)]
enum CharRange {
    AsciiControl,
    AsciiPrintable,
    TwoByte,
    ThreeByte,
    FourByte, // Requires UTF-16 surrogate pairs
}

impl CharRange {
    fn random_char(&self, rng: &mut impl RngExt) -> char {
        let x = match self {
            Self::AsciiControl => rng.random_range(0x00..=0x1f),
            Self::AsciiPrintable => rng.random_range(0x20..=0x7f),
            Self::TwoByte => rng.random_range(0x80..=0x7ff),
            Self::ThreeByte => {
                if rng.random_bool(0.73) {
                    rng.random_range(0x800..=0xd7ff)
                } else {
                    rng.random_range(0xe000..=0xffff)
                }
            }
            Self::FourByte => rng.random_range(0x10000..=0x10ffff),
        };

        match char::from_u32(x) {
            Some(c) => c,
            None => unreachable!("invalid character: {x:#x} for range {self:?}"),
        }
    }

    fn random_char_byte_range(byte_rng: RangeInclusive<usize>, rng: &mut impl RngExt) -> char {
        assert!(
            byte_rng.start() <= byte_rng.end(),
            "byte range cannot be empty, but {byte_rng:?} was given"
        );
        assert!(
            1 <= *byte_rng.start() && *byte_rng.end() <= 4,
            "byte range must be contained within 1..=4, but {byte_rng:?} was given"
        );

        let (hat, weights) = Self::random_char_byte_range_setup(byte_rng);

        let dist = WeightedIndex::new(&weights).unwrap();
        let drawn = hat[dist.sample(rng)];

        drawn.random_char(rng)
    }

    fn random_char_byte_range_setup(
        byte_rng: RangeInclusive<usize>,
    ) -> (SmallVec<[CharRange; 5]>, SmallVec<[f64; 5]>) {
        let mut hat = SmallVec::<[CharRange; 5]>::new();
        let mut weights = SmallVec::<[f64; 5]>::new();

        if byte_rng.contains(&1) {
            hat.push(Self::AsciiControl);
            weights.push(0.10);
            hat.push(Self::AsciiPrintable);
            weights.push(0.90);
        }

        if byte_rng.contains(&2) {
            hat.push(Self::TwoByte);
            weights.push(0.15);
        }

        if byte_rng.contains(&3) {
            hat.push(Self::ThreeByte);
            weights.push(0.15);
        }

        if byte_rng.contains(&4) {
            hat.push(Self::FourByte);
            weights.push(0.15);
        }

        (hat, weights)
    }
}

struct Seps {
    struct_sep: Vec<u8>,
    val_sep: Vec<u8>,
    inline_space: u8,
    indent: usize,
}

impl Seps {
    fn new(white_rules: &WhiteRules) -> Self {
        let line_break = white_rules.line_break();
        let indent = white_rules.indent();

        let mut struct_sep = Vec::with_capacity(line_break.len() + 16 * indent);
        struct_sep.extend_from_slice(line_break);

        let mut val_sep = Vec::with_capacity(line_break.len() + 1 + 16 * indent);
        val_sep.push(b',');
        val_sep.extend_from_slice(line_break);

        Self {
            struct_sep,
            val_sep,
            inline_space: white_rules.inline_space().unwrap_or(b' '),
            indent,
        }
    }

    fn push_level(&mut self) {
        self.struct_sep
            .resize(self.struct_sep.len() + self.indent, self.inline_space);
        self.val_sep
            .resize(self.val_sep.len() + self.indent, self.inline_space);
    }

    fn pop_level(&mut self) {
        self.struct_sep
            .truncate(self.struct_sep.len() - self.indent);
        self.val_sep.truncate(self.val_sep.len() - self.indent);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bufjson::lexical::{Token, fixed::FixedAnalyzer};
    use rand::{SeedableRng, rngs::StdRng};
    use rstest::rstest;

    #[rstest]
    // #[case(2)]
    // #[case(3)]
    // #[case(4)]
    // #[case(5)]
    // #[case(10)]
    // #[case(20)]
    // #[case(50)]
    // #[case(100)]
    // #[case(8 * 1024)]
    // #[case(16 * 1024)]
    #[case(10 * 1024 * 1024)]
    fn test_generator_default_obj(#[case] len: usize) {
        let mut g = Generator::default()
            .with_rng(StdRng::seed_from_u64(len as u64))
            .with_root(Root::Obj)
            .with_white_rules(WhiteRules::pretty(LineSep::N, b' ', 2));
        let mut buf = Vec::new();

        g.generate(len, &mut buf).unwrap();

        assert_eq!(len, buf.len());

        let mut parser = FixedAnalyzer::new(buf.clone()).into_parser();
        loop {
            match parser.next() {
                Token::Eof => {
                    assert_eq!(len, parser.pos().offset);

                    break;
                }
                Token::Err => {
                    let pos = *parser.pos();
                    let err = parser.err();

                    let msg = format!("{err}");

                    eprintln!("{msg}");
                    eprintln!("    parser pos: {pos}");
                    eprintln!("    error detail: {err:?}");
                    eprintln!("-------------------- JSON --------------------");
                    eprintln!("{}", String::from_utf8(buf).unwrap());

                    panic!("{msg}");
                }
                _ => continue,
            }
        }
    }
}
