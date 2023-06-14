#[flux::refined_by(lo: int, hi: int)]
pub struct RngIter {
    #[flux::field(usize[@lo])]
    _lo: usize,
    #[flux::field(usize[@hi])]
    hi: usize,
    #[flux::field(usize{v:lo <= v && v <= hi})]
    cur: usize,
}

impl RngIter {
    #[flux::sig(fn(lo: usize, hi: usize{lo <= hi}) -> RngIter[lo, hi])]
    pub fn new(lo: usize, hi: usize) -> RngIter {
        Self {
            _lo: lo,
            hi,
            cur: lo,
        }
    }
}

#[flux::refined_by(lo: int, hi: int)]
pub struct Rng {
    #[flux::field(usize[@lo])]
    lo: usize,
    #[flux::field({usize[@hi] | lo <= hi})]
    hi: usize,
}

impl Rng {
    #[flux::sig(fn(lo:usize, hi:usize{lo <= hi}) -> Rng[lo, hi])]
    pub fn new(lo: usize, hi: usize) -> Rng {
        Self { lo, hi }
    }
}

impl Iterator for RngIter {
    type Item = usize;

    #[flux::sig(fn(self: &mut RngIter[@lo, @hi]) -> Option<usize{v: lo <= v && v < hi}>)]
    fn next(&mut self) -> Option<usize> {
        let cur = self.cur;
        let hi = self.hi;
        if cur < hi {
            self.cur = cur + 1;
            Some(cur)
        } else {
            None
        }
    }
}

impl IntoIterator for Rng {
    type Item = usize;
    type IntoIter = RngIter;

    #[flux::sig(fn(Rng[@lo, @hi]) -> RngIter[lo, hi])]
    fn into_iter(self) -> RngIter {
        RngIter::new(self.lo, self.hi)
    }
}

impl RngIter {
    pub fn ffold<B, F>(&mut self, init: B, mut f: F) -> B
    where
        F: FnMut(B, usize) -> B,
    {
        let mut res = init;
        while let Some(i) = self.next() {
            res = f(res, i);
        }
        res
    }
}

#[flux::sig(fn(lo:usize, hi:usize{lo <= hi}) -> Rng[lo, hi])]
pub fn range(lo: usize, hi: usize) -> Rng {
    Rng::new(lo, hi)
}
