use crate::rvec::{self, AsRVec as _, RVec, rvec};
use flux_rs::assert;
use flux_rs::attrs::*;
use rand::{Rng, rngs::ThreadRng};

fn test() {
    assert(10 < 20)
}

fn sigmoid(x: f64) -> f64 {
    1.0 / (1.0 + (-x).exp())
}

#[spec(fn(&RVec<f64>[@n], &RVec<f64>[n]) -> f64)]
fn dot_product(a: &RVec<f64>, b: &RVec<f64>) -> f64 {
    let mut sum = 0.0;
    for i in 0..a.len() {
        sum += a[i] * b[i];
    }
    sum
}

#[spec(fn(&RVec<f64>[@n], &RVec<f64>[n]) -> f64)]
fn dot_product2(a: &RVec<f64>, b: &RVec<f64>) -> f64 {
    (0..a.len()).map(|i| (a[i] * b[i])).sum()
}

// HT: https://byteblog.medium.com/building-a-simple-neural-network-from-scratch-in-rust-3a7b12ed30a9

// Define the structure of a single layer in the network
#[refined_by(i: int, o: int)]
struct Layer {
    #[field(usize[i])]
    num_inputs: usize,

    #[field(usize[o])]
    num_outputs: usize,

    #[field(RVec<RVec<f64>[i]>[o])]
    weight: RVec<RVec<f64>>,

    #[field(RVec<f64>[o])]
    bias: RVec<f64>,

    #[field(RVec<f64>[o])]
    outputs: RVec<f64>,
}

#[opts(check_overflow = "lazy")]
#[spec(fn(n: usize[100]) -> usize[101])]
fn foo(n: usize) -> usize {
    let m = n + 1;
    m
}

#[spec(fn(n: usize, f:F) -> RVec<A>[n]
       where F: FnMut(usize{v:0<=v && v < n}) -> A)]
fn init0<F, A>(n: usize, mut f: F) -> RVec<A>
where
    F: FnMut(usize) -> A,
{
    let mut i = 0;
    let mut res = RVec::new();
    while i < n {
        res.push(f(i));
        i += 1;
    }
    res
}

#[spec(fn(n: usize, f:F) -> RVec<A>[n]
       where F: FnMut(usize{v:0<=v && v < n}) -> A)]
fn init<F, A>(n: usize, mut f: F) -> RVec<A>
where
    F: FnMut(usize) -> A,
{
    let mut res = RVec::new();
    for i in 0..n {
        res.push(f(i));
    }
    res
}

#[spec(fn(n: usize, f:F) -> RVec<A>[n] where F: FnMut(usize{v:0<=v && v < n}) -> A)]
fn init2<F, A>(n: usize, mut f: F) -> RVec<A>
where
    F: FnMut(usize) -> A,
{
    (0..n).map(|i| f(i)).collect()
}

#[spec(fn(input_size: usize, output_size: usize) -> RVec<RVec<f64>[input_size]>[output_size])]
fn mk_weights(input_size: usize, output_size: usize) -> RVec<RVec<f64>> {
    let mut rng = rand::thread_rng();
    let weights = init2(output_size, |_| {
        init2(input_size, |_| rng.gen_range(-1.0..1.0))
    });
    weights
}

impl Layer {
    #[spec(fn(i: usize, o: usize) -> Layer[i, o])]
    fn new(i: usize, o: usize) -> Layer {
        let mut rng = rand::thread_rng();
        Layer {
            num_inputs: i,
            num_outputs: o,
            weight: init(o, |_| init(i, |_| rng.gen_range(-1.0..1.0))),
            bias: init(o, |_| rng.gen_range(-1.0..1.0)),
            outputs: init(o, |_| 0.0),
        }
    }

    #[spec(fn(&mut Layer[@l], &RVec<f64>[l.i]) )]
    fn forward(&mut self, input: &RVec<f64>) {
        (0..self.num_outputs).for_each(|i| {
            let weighted_input = dot_product(&self.weight[i], input);
            self.outputs[i] = sigmoid(weighted_input + self.bias[i])
        })
    }

    #[spec(fn(&mut Layer[@l], &RVec<f64>[l.i], &RVec<f64>[l.o], _) -> RVec<f64>[l.i])]
    fn backward(&mut self, inputs: &RVec<f64>, error: &RVec<f64>, learning_rate: f64) -> RVec<f64> {
        let mut input_error = rvec![0.0; inputs.len()];
        for i in 0..self.num_outputs {
            for j in 0..self.num_inputs {
                input_error[j] += self.weight[i][j] * error[i];
                self.weight[i][j] -= learning_rate * error[i] * inputs[j];
            }
            self.bias[i] -= learning_rate * error[i];
        }
        input_error
    }

    #[spec(fn(&mut Layer[@l], &RVec<f64>[l.i]) -> RVec<f64>[l.o])]
    fn ooforward(self: &mut Layer, input: &RVec<f64>) -> RVec<f64> {
        (0..self.num_outputs)
            .map(|i| {
                let wt_in = dot_product(&self.weight[i], input);
                sigmoid(wt_in + self.bias[i])
            })
            .collect()
    }
}

#[spec(fn(&RVec<f64>[@n], &RVec<f64>[n]) -> f64)]
fn mean_squared_error(predicted: &RVec<f64>, actual: &RVec<f64>) -> f64 {
    (0..predicted.len())
        .map(|i| (predicted[i] - actual[i]).powi(2))
        .sum::<f64>()
        / predicted.len() as f64
}

#[spec(fn(&[f64][5]))]
fn test_enumerate(vec: &[f64]) {
    let mut iter = vec.iter().enumerate();
    assert(iter.next().is_some());
    assert(iter.next().is_some());
    assert(iter.next().is_some());
    assert(iter.next().is_some());
    assert(iter.next().is_some());
    // assert(iter.next().is_some());
}

// -------------------------------------------------------------------------------------

#[refined_by(i: int, o: int)]
enum NeuralNetwork {
    #[variant((Layer[@i, @o]) -> NeuralNetwork[i, o])]
    Last(Layer),

    #[variant((Layer[@i, @h], Box<NeuralNetwork[h, @o]>) -> NeuralNetwork[i, o])]
    Next(Layer, Box<NeuralNetwork>),
}

impl NeuralNetwork {
    /// Create a new neural network with the given input size, hidden layer sizes, and output size.
    #[spec(fn(input_size: usize, hidden_sizes: &[usize], output_size: usize) -> NeuralNetwork[input_size, output_size])]
    fn new(input_size: usize, hidden_sizes: &[usize], output_size: usize) -> NeuralNetwork {
        if hidden_sizes.len() == 0 {
            NeuralNetwork::Last(Layer::new(input_size, output_size))
        } else {
            let n = hidden_sizes[0];
            let rest = NeuralNetwork::new(n, &hidden_sizes[1..], output_size);
            let layer = Layer::new(input_size, n);
            NeuralNetwork::Next(layer, Box::new(rest))
        }
    }

    #[spec(fn(&mut NeuralNetwork[@i, @o], &RVec<f64>[i]) -> RVec<f64>[o])]
    fn forward(&mut self, input: &RVec<f64>) -> RVec<f64> {
        match self {
            NeuralNetwork::Last(layer) => {
                layer.forward(input);
                layer.outputs.clone()
            }
            NeuralNetwork::Next(layer, next) => {
                layer.forward(input);
                next.forward(&layer.outputs)
            }
        }
    }

    /// Backpropagation algorithm: assumes we have already done a "forwards" pass with
    /// the results stored in each `Layer`'s `outputs` field.
    #[spec(fn(&mut NeuralNetwork[@i, @o], &RVec<f64>[i], &RVec<f64>[o], _) -> RVec<f64>[i])]
    fn backward(
        &mut self,
        inputs: &RVec<f64>,
        target: &RVec<f64>,
        learning_rate: f64,
    ) -> RVec<f64> {
        match self {
            NeuralNetwork::Last(layer) => {
                let error = (0..layer.num_outputs)
                    .map(|i| layer.outputs[i] - target[i])
                    .collect();
                layer.backward(inputs, &error, learning_rate)
            }
            NeuralNetwork::Next(layer, next) => {
                let error = next.backward(&layer.outputs, target, learning_rate);
                layer.backward(inputs, &error, learning_rate)
            }
        }
    }
}
