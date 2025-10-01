use std::ops::Range;
use flux_rs::attrs::*;
use flux_rs::assert;
use crate::rvec::*;

#[refined_by(rows: int, cols: int, nnz: int)]
struct CSRMatrix {
    #[field(usize[rows])]
    rows: usize,

    #[field(usize[cols])]
    cols: usize,

    #[field(RVec<f64>[nnz])]
    values: RVec<f64>,

    #[field(RVec<usize{v:v < cols}>[nnz])]
    col_index: RVec<usize>,

    #[field(RVec<usize{v: v <= nnz}>[rows + 1])]
    row_index: RVec<usize>,
}

/*
example 1:

[ [ 5, 0, 0, 0 ],
  [ 0, 8, 0, 0 ],
  [ 0, 0, 3, 0 ],
  [ 0, 6, 0, 0 ] ]
*/

fn example1() -> CSRMatrix {
    CSRMatrix {
        rows: 4,
        cols: 4,
        values: rvec![5.0, 8.0, 3.0, 6.0],
        col_index: rvec![0, 1, 2, 1],
        row_index: rvec![0, 1, 2, 3, 4],
    }
}

/*
example 2:
 [[10, 20, 0, 0, 0, 0],
  [0, 30, 0, 40, 0, 0],
  [0, 0, 50, 60, 70, 0],
  [0, 0, 0, 0, 0, 80]]
*/

fn example2() -> CSRMatrix {
    CSRMatrix {
        rows: 4,
        cols: 6,
        values: rvec![10.0, 20.0, 30.0, 40.0, 50.0, 60.0, 70.0, 80.0],
        col_index: rvec![0, 1, 1, 3, 2, 3, 4, 5],
        row_index: rvec![0, 2, 4, 7, 8],
    }
}


impl CSRMatrix {

    #[spec(fn new(rows: usize, cols: usize, mat: RVec<RVec<f64>[cols]>[rows]) -> CSRMatrix)]
    fn new(rows: usize, cols: usize, mat: RVec<RVec<f64>>) -> CSRMatrix {
        let mut nnz = 0;
        let mut col_index = RVec::new();
        let mut row_index = RVec::new();
        let mut values = RVec::new();

        for i in 0..rows {
            row_index.push(nnz);
            for j in 0..cols {
                let val = mat[i][j];
                if val != 0.0 {
                    col_index.push(j);
                    values.push(val);
                    nnz += 1;
                }
            }
        }
        row_index.push(nnz); // EXERCISE: delete this for bug!

        CSRMatrix { rows, cols, values, col_index, row_index }
    }

    // EXERCISE: implement a method to get the value at (row, col)
    #[spec(fn get(&Self[@self], row: usize{row < self.rows}, col: usize{col < self.cols}) -> f64)]
    fn get(&self, row: usize, col: usize) -> f64 {
        let start = self.row_index[row];
        let end = self.row_index[row + 1];
        for i in start..end {
            if self.col_index[i] == col {
                return self.values[i];
            }
        }
        0.0
    }

    #[spec(fn multiply(&Self[@self], vec: &RVec<f64>[self.cols]) -> RVec<f64>[self.rows])]
    fn multiply(&self, vec: &RVec<f64>) -> RVec<f64> {
        let mut result = RVec::from_elem_n(0.0, self.rows);
        for i in 0..self.rows {
            let start = self.row_index[i];
            let end = self.row_index[i + 1];
            for j in start..end {
                let col = self.col_index[j];
                result[i] += self.values[j] * vec[col];
            }
        }
        result
    }
}

fn test_assert() {
    assert(1 < 2); // ERROR
}
