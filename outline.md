
## Outline for SOAP 2023 Talk

### Intro

### Programs

1. Index with PURE values:
   * Index with PURE values:
        * bool: tt, ff, assert
        * usize: five, six, twelve
        * RVec: RVec<i32>[0], RVec<i32>[5] // literals

   * Refine parameters
        * fn len(x: &RVec<i32>[n]) -> usize[n]

   * Existential
        * pos usize{v:0 < v}
           - fdiv + assert
        * RVec::get     //
           - dist       // while
           - min_index  // while

2. Update refinements for owned locations
   * `foo` example x += 10
   * `min_index` with while

3. &mut T
   * SLIDES
   * **TODO: RVEC: `set`**
   * **TODO: `kmeans::plus`** (in place update)

4. &strg T
   * slides
   * **TODO: RVEC: `push`**
   * **TODO: RVEC: range**

5. Putting it all together
   * DEMO: map/reduce/kmeans

### Analysis
   * **TODO: range: constraints**
   * **TODO: min_index+fold: constraints**

### Results
