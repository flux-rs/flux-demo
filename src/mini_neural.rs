use crate::rvec::RVec;

fn random() -> f64 {
    0.0
}

fn sigmoid(x: f64) -> f64 {
    1.0 / (1.0 + (-x).exp())
}

fn dot_product(x: &RVec<f64>, y: &RVec<f64>) -> f64 {
    let mut sum = 0.0;
    for i in 0..x.len() {
        sum += x[i] * y[i];
    }
    sum
}

fn init<T, F>(n: usize, mut f: F) -> RVec<T>
where
    F: FnMut(usize) -> T,
{
    let mut res = RVec::new();
    for i in 0..n {
        res.push(f(i));
    }
    res
}

fn mk_weights(input_size: usize, output_size: usize) -> RVec<RVec<f64>> {
    init(output_size, |_| init(input_size, |_| random()))
}

fn forward(weights: &RVec<RVec<f64>>, inputs: &RVec<f64>) -> RVec<f64> {
    let mut outputs = RVec::new();
    for i in 0..weights.len() {
        let weighted_input = dot_product(&weights[i], inputs);
        outputs.push(sigmoid(weighted_input))
    }
    outputs
}

pub fn test(inputs: &RVec<f64>, outputs: &mut RVec<f64>) -> RVec<f64> {
    let weights = mk_weights(inputs.len(), outputs.len());
    forward(&weights, inputs)
}
