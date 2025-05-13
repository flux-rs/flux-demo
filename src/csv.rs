// https://ucsd-progsys.github.io/liquidhaskell-blog/2013/10/10/csv-tables.lhs/

use crate::rvec::RVec;
use flux_rs::attrs::*;
#[refined_by(cols: int)]
pub struct CSV {
    #[field(RVec<String>[cols])]
    pub header: RVec<String>,
    #[field(RVec<RVec<String>[cols]>)]
    pub row_vals: RVec<RVec<String>>,
}

impl CSV {
    #[spec(fn (vals: &[_][@n]) -> RVec<String>[n])]
    fn convert(vals: &[&str]) -> RVec<String> {
        RVec::from_slice(vals).map(|s| s.to_string())
    }

    #[spec(fn (header: &[&str][@n]) -> CSV[n])]
    pub fn new(header: &[&str]) -> Self {
        CSV {
            header: Self::convert(header),
            row_vals: RVec::new(),
        }
    }

    #[spec(fn (&mut Self[@n], row: &[_][n]))]
    pub fn push(&mut self, row: &[&str]) {
        self.row_vals.push(Self::convert(row))
    }

    #[spec(fn (&Self[@n]) -> usize[n])]
    pub fn cols(&self) -> usize {
        self.header.len()
    }
}

#[trusted]
#[spec(fn(slice: &[T][@n]) -> usize[n])]
fn slice_len<T>(slice: &[T]) -> usize {
    slice.len()
}

#[spec(fn(head: &[&str][@N], rows: &[&[&str]]) -> Option<CSV[N]>)]
fn csv_opt(head: &[&str], rows: &[&[&str]]) -> Option<CSV> {
    let mut csv = CSV::new(head);
    let n = csv.cols();
    for row in rows {
        if slice_len(row) == n {
            csv.push(row);
        } else {
            return None; // invalid row!
        }
    }
    Some(csv)
}

#[spec(fn() -> Option<CSV[2]>)]
fn test1() -> Option<CSV> {
    csv_opt(
        &["Item", "Price"],
        &[
            &["Espresso", "2.25"],
            &["Macchiato", "2.75"],
            &["Cappucino", "3.35"],
            &["Americano", "2.25"],
        ],
    )
}

#[spec(fn (head: [&str;_], rows: &[_]) -> CSV[N])]
fn csv<const N: usize>(head: [&str; N], rows: &[[&str; N]]) -> CSV {
    let header = RVec::from_array(head).map(|s| s.to_string());
    let mut row_vals = RVec::new();
    for row in rows {
        row_vals.push(RVec::from_slice(row).map(|s| s.to_string()));
    }
    CSV { header, row_vals }
}

#[spec(fn() -> CSV[2])]
fn test2() -> CSV {
    csv(
        ["Item", "Price"],
        &[
            ["Espresso", "2.25"],
            ["Macchiato", "2.75"],
            ["Cappucino", "3.35"],
            ["Americano", "2.25"],
        ],
    )
}

#[macro_export]
macro_rules! mk_csv {
    ($header:expr $(,$row:expr)* $(,)?) => {{
        let mut csv = CSV::new($header);
        $( csv.push($row); )*
        csv
    }}
}

#[spec(fn() -> CSV[2])]
fn test3() -> CSV {
    mk_csv!(
        &["Item", "Price"],
        &["Espresso", "2.25"],
        &["Macchiato", "2.75"],
        &["Cappucino", "3.35"],
        &["Americano", "2.25"],
    )
}
