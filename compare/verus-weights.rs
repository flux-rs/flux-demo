verus! {

fn init<F, A>(n: usize, mut f: F) -> (res: Vec<A>)
where
    F: FnMut(usize) -> A,
requires
    forall| i: usize | 0 <= i < n ==> call_requires(f, (i,)),
ensures
    res.len() == n,
    forall| i: usize | 0 <= i < n ==> call_ensures(f, (i,), #[trigger] res[i as int])
{
    let mut i = 0;
    let mut res = Vec::new();
    while i < n
        invariant
            forall| i: usize | 0 <= i < n ==> call_requires(f, (i,)),
            i <= n,
            res.len() == i,
            forall| j: usize | 0 <= j < i ==> call_ensures(f, (j,), #[trigger] res[j as int])
        decreases
            n - i,
    {
        res.push(f(i));
        i += 1;
    }
    res
}

fn mk_weights(input_size: usize, output_size: usize) -> (res: Vec<Vec<u64>>)
    ensures
        res.len() == output_size,
        forall| i: usize | 0 <= i < output_size ==> #[trigger] res[i as int].len() == input_size,
{
    let lambda_input_size = |i: usize|  -> (res: Vec<u64>)
        ensures
            res.len() == input_size,
    {
        init(input_size, |j| 0)
    };

    let weights = init(output_size, lambda_input_size);
    weights
}

fn max(a: u64, b: u64) -> u64 {
    if a > b { a } else { b }
}

fn main() {
    let input_size = 10;
    let output_size = 5;
    let weights = mk_weights(input_size, output_size);
    let mut res = 0;
    let mut i = 0;
    while i < output_size
        invariant
            weights.len() == output_size,
            forall| l: usize | 0 <= l < output_size ==> #[trigger] weights[l as int].len() == input_size,
        decreases
            output_size - i,
    {
        let mut j = 0;
        while j < input_size
            invariant
                weights.len() == output_size,
                forall| l: usize | 0 <= l < output_size ==> #[trigger] weights[l as int].len() == input_size,
                0 <= j <= input_size,
                0 <= i < output_size,
            decreases
                input_size - j,
        {
            assert(weights[i as int].len() == input_size);
            res = max(res, weights[i][j]);
            j += 1;
        }
        i += 1;
    }
}
}
