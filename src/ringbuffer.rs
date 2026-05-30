use flux_rs::{opaque, refined_by, spec, trusted};

flux_rs::defs! {

    fn min(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    fn is_init(len: int, num_enqueues: int, index: int) -> bool {
        0 <= index && index < min(num_enqueues, len)
    }

    fn rb_len(rb: RingBuffer) -> int {
         if rb.tl > rb.hd { rb.tl - rb.hd }
        else if rb.tl < rb.hd { rb.len - rb.hd + rb.tl }
        else { 0 }
    }

    fn rb_is_full(rb: RingBuffer) -> bool {
        rb.hd == (rb.tl + 1) % rb.len
    }

    fn rb_is_empty(rb: RingBuffer) -> bool {
        rb.hd == rb.tl
    }

    fn rb_is_valid(rb: RingBuffer, index: int) -> bool {
        ((index + rb.len - rb.hd) % rb.len) < rb_len(rb)
    }
}

// ======== Extern specs ========

mod flux_specs {
    #[flux_rs::extern_spec]
    #[flux_rs::refined_by(b: bool)]
    enum Option<T> {
        #[variant(Option<T>[false])]
        None,
        #[variant({T} -> Option<T>[true])]
        Some(T),
    }
}

// Ghost "counter" type; will be used to count the number of enqueues in the ring buffer.
#[opaque]
#[refined_by(n: int)]
pub struct Ghost;

impl Ghost {
    #[trusted]
    #[spec(fn () -> Self[0])]
    pub fn new() -> Self {
        Self
    }
    #[trusted]
    #[spec(fn (me: &mut Self[@n]) ensures me: Self[n+1])]
    pub fn bump(&mut self) {}
}
// ===== FluxSlice ============================================================

#[flux_rs::opaque]
#[flux_rs::refined_by(len: int, hdl get: int -> bool)]
#[repr(transparent)]
pub struct FluxSlice<'a, T>(&'a mut [T]);

impl<'a, T> FluxSlice<'a, T> {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&mut [T][@n]) -> FluxSlice<T>{fs: fs.len == n})]
    pub fn from_mut(slice: &'a mut [T]) -> Self {
        // SAFETY: FluxSlice<T> is repr(transparent) over [T]
        // EVAN? unsafe { &mut *(slice as *mut [T] as *mut FluxSlice<T>) }
        FluxSlice(slice)
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&FluxSlice<T>[@n, @f]) -> usize[n])]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn(&FluxSlice<T>[@n, @f], index: usize{index < n && f(index)}) -> T)]
    pub fn get(&self, index: usize) -> T
    where
        T: Copy,
    {
        self.0[index]
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &mut FluxSlice<T>[@n, @f], index: usize{index < n}, val: T)
        ensures self: FluxSlice<T>[n, |j| j == index || f(j)]
    )]
    pub fn set(&mut self, index: usize, val: T) {
        self.0[index] = val;
    }
}

// ===== RingBuffer ==========================================================

#[flux_rs::refined_by(len: int, hd: int, tl: int, num_enqueues: int)]
#[flux_rs::invariant(0 < len && 0 <= hd && hd < len && 0 <= tl && tl < len && 0 <= num_enqueues)]
#[flux_rs::invariant(num_enqueues < len => (tl == num_enqueues && hd <= tl))]
pub struct RingBuffer<'a, T: Copy + 'a> {
    #[flux_rs::field(FluxSlice<T>[len, |idx| is_init(len, num_enqueues, idx)])]
    ring: FluxSlice<'a, T>,
    #[flux_rs::field(usize[hd])]
    head: usize,
    #[flux_rs::field(usize[tl])]
    tail: usize,
    #[flux_rs::field(Ghost[num_enqueues])]
    ghost: Ghost,
}

impl<'a, T: Copy> RingBuffer<'a, T> {
    #[flux_rs::sig(fn({FluxSlice<T>[@len, |i| false] | 0 < len}) -> RingBuffer<T>[len, 0, 0, 0])]
    pub fn new(ring: FluxSlice<'a, T>) -> RingBuffer<'a, T> {
        RingBuffer {
            head: 0,
            tail: 0,
            ring,
            ghost: Ghost::new(),
        }
    }

    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> bool[rb_is_full(s)])]
    pub fn is_full(&self) -> bool {
        self.head == ((self.tail + 1) % self.ring.len())
    }

    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> bool[!rb_is_empty(s)])]
    fn has_elements(&self) -> bool {
        self.head != self.tail
    }

    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s]) -> usize[rb_len(s)])]
    fn len(&self) -> usize {
        if self.tail > self.head {
            self.tail - self.head
        } else if self.tail < self.head {
            (self.ring.len() - self.head) + self.tail
        } else {
            0
        }
    }

    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: usize) -> bool[rb_is_valid(s, index)])]
    fn is_valid(&self, index: usize) -> bool {
        let capacity = self.ring.len();
        let position_in_ring = (index + capacity - self.head) % capacity;
        position_in_ring < self.len()
    }

    #[flux_rs::sig(fn(self: &RingBuffer<T>[@s], index: usize{index < s.len}) -> Option<T>[rb_is_valid(s, index)])]
    fn get_internal(&self, index: usize) -> Option<T> {
        if !self.is_valid(index) {
            None
        } else {
            Some(self.ring.get(index))
        }
    }

    #[flux_rs::sig(fn(self: &strg RingBuffer<T>[@s], val: T) -> bool[#b] ensures self: RingBuffer<T>{ v: v.num_enqueues == if b { s.num_enqueues + 1 } else { s.num_enqueues } })]
    pub fn enqueue(&mut self, val: T) -> bool {
        if self.is_full() {
            false
        } else {
            self.ring.set(self.tail, val);
            self.tail = (self.tail + 1) % self.ring.len();
            self.ghost.bump();
            true
        }
    }

    #[flux_rs::sig(fn(self: &strg RingBuffer<T>[@s]) -> Option<T> ensures self: RingBuffer<T>)]
    pub fn dequeue(&mut self) -> Option<T> {
        if self.head != self.tail {
            let val = self.get_internal(self.head);
            self.head = (self.head + 1) % self.ring.len();
            val
        } else {
            None
        }
    }
}

// TODO: top-level invariant
// index < s.ring.len && is_valid(index) => s.ring.init(index)
// maybe implement something based on the fact that empty => hd is valid?

// TODO: more complex methods
// TODO: back to MaybeUninit
// TODO: remove FluxSlice
