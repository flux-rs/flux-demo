#import "@preview/codly:1.2.0": *
#show: codly-init

#codly(
  highlight-inset: (x: 0.32em, y: 0pt),
  highlight-outset: (x: 0pt, y: 0.32em),
  highlights: ((line: 2, start: 15, end: 19, fill: red),),
)
```rust
fn test(x) {
  let apple = x + 1;
  let cat = [apple, buck];
  let buck = a + 1;
  return c
}
```



// #codly(
//   zebra-fill: none,
//   inset: 0.3em,
//   number-format: none,
//   languages: (
//     rust: (
//       color: white,
//     )
//   )
// )
