# `Schematic.Math`

A reusable Lean mathematics library developed using Schematic's autonomous proof engine Hydra.

## Packages

Under the `Schematic.Math` namespace:

- [`GraphTheory`](Schematic/Math/GraphTheory.lean): finite graph theory, strict subdivisions, planar embeddings, hypermaps, Kuratowski's theorem, and graph minors.

## Related work

Also formalized by Schematic Hydra:

- [`FourColorTheorem`](https://github.com/schematic-rs/formalized-fct): the Four Color Theorem (FCT).
- [`DominatingFourColour`](https://github.com/schematic-rs/formalized-2605.10112): a significant strengthening of the FCT proved by António Girão, Freddie Illingworth, Bojan Mohar, Sergey Norin, Raphael Steiner, Youri Tamitegama, Jane Tan, David R. Wood, and Jung Hon Yip ([arXiv:2605.10112](https://arxiv.org/abs/2605.10112)).

## Build

```sh
lake update
lake build
```

## License

Apache-2.0. See `LICENSES/Apache-2.0.txt`.
