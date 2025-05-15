use flux_rs::attrs::*;
use rand::{Rng, rngs::ThreadRng};

use crate::rvec::{self, AsRVec as _, RVec, rvec};

#[spec(fn(bool[true]))]
fn assert(_b: bool) {}

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
#[refined_by(input_size: int, output_size: int)]
struct Layer {
    /// number of input values
    #[field(usize[input_size])]
    input_size: usize,

    /// number of output neurons
    #[field(usize[output_size])]
    output_size: usize,

    /// vector of weights for each output neuron
    #[field(RVec<RVec<f64>[input_size]>[output_size])]
    weights: RVec<RVec<f64>>,

    /// biases for each output neuron
    #[field(RVec<f64>[output_size])]
    biases: RVec<f64>,

    /// values computed as output of the layer
    #[field(RVec<f64>[output_size])]
    outputs: RVec<f64>,
}

#[spec(fn(n: usize, f:F) -> RVec<A>[n] where F: FnMut(usize{v:0<=v && v < n}) -> A)]
fn fill_vec<F, A>(n: usize, mut f: F) -> RVec<A>
where
    F: FnMut(usize) -> A,
{
    // let mut res = RVec::new();
    // for i in 0..n {
    //     res.push(f(i));
    // }
    // res
    (0..n).map(|i| f(i)).collect()
}

#[spec(fn(input_size: usize, output_size: usize) -> RVec<RVec<f64>[input_size]>[output_size])]
fn mk_weights(input_size: usize, output_size: usize) -> RVec<RVec<f64>> {
    let mut rng = rand::thread_rng();
    let weights = fill_vec(output_size, |_| {
        fill_vec(input_size, |_| rng.gen_range(-1.0..1.0))
    });
    weights
}

impl Layer {
    #[spec(fn(input_size: usize, output_size: usize) -> Layer[input_size, output_size])]
    fn new(input_size: usize, output_size: usize) -> Layer {
        let mut rng = rand::thread_rng();

        let weights = fill_vec(output_size, |_| {
            fill_vec(input_size, |_| rng.gen_range(-1.0..1.0))
        });

        let biases = fill_vec(output_size, |_| rng.gen_range(-1.0..1.0));

        let outputs = fill_vec(output_size, |_| 0.0);

        Layer {
            input_size,
            output_size,
            weights,
            biases,
            outputs,
        }
    }

    #[spec(fn(&mut Layer[@l], &RVec<f64>[l.input_size]) )]
    fn forward(&mut self, input: &RVec<f64>) {
        (0..self.output_size).for_each(|i| {
            let weighted_input = dot_product(&self.weights[i], input);
            self.outputs[i] = sigmoid(weighted_input + self.biases[i])
        })
    }

    #[spec(fn(&mut Layer[@l], &RVec<f64>[l.input_size], &RVec<f64>[l.output_size], _) -> RVec<f64>[l.input_size])]
    fn backward(&mut self, inputs: &RVec<f64>, error: &RVec<f64>, learning_rate: f64) -> RVec<f64> {
        let mut input_error = rvec![0.0; inputs.len()];
        for i in 0..self.output_size {
            for j in 0..self.input_size {
                input_error[j] += self.weights[i][j] * error[i];
                self.weights[i][j] -= learning_rate * error[i] * inputs[j];
            }
            self.biases[i] -= learning_rate * error[i];
        }
        input_error
    }
}

#[spec(fn(&RVec<f64>[@n], &RVec<f64>[n]) -> f64)]
fn mean_squared_error(predicted: &RVec<f64>, actual: &RVec<f64>) -> f64 {
    (0..predicted.len())
        .map(|i| (predicted[i] - actual[i]).powi(2))
        .sum::<f64>()
        / predicted.len() as f64
}

// -------------------------------------------------------------------------------------

#[refined_by(input_size: int, output_size: int)]
enum NeuralNetwork {
    #[variant((Layer[@l]) -> NeuralNetwork[l.input_size, l.output_size])]
    Last(Layer),

    #[variant((Layer[@input_size, @n], Box<NeuralNetwork[n, @output_size]>) -> NeuralNetwork[input_size, output_size])]
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
                let error = (0..layer.output_size)
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
