# Contributors

[Back to the README](../README.md)

AI models wrote the mathematics and the Lean code. The repository owner
directed the work, reviewed it, and made the decisions about scope and naming.
Times are rough commit times, in US Central time (UTC−5).

## 22 September 2026

* **Around 12:00 — three squares by enumeration.** ChatGPT 6 Pro wrote a
  certificate proof of the three-square optimum: separating axes, 48 branches
  and 53 rational certificates. Claude Opus 5 High-Max compiled it and
  arranged the repository. It is kept on the `legacy` branch.
* **15:00 to 16:15 — three, four and five squares by occupied arcs.**
  Following an idea from Claude Opus 5 Max, ChatGPT 6 Pro wrote one framework
  for all three cases
  ([PR #2](https://github.com/vltanh/lean4-squares-in-circles/pull/2)).
  Claude Opus 5.5 Max compiled it and made it the main proof.
* **16:45 to 19:50 — uniqueness.** ChatGPT 6 Pro wrote the uniqueness proofs
  for three, four and five squares
  ([PR #3](https://github.com/vltanh/lean4-squares-in-circles/pull/3)), and
  Claude Opus 5.5 Max compiled them.
* **Around 21:15 — one and two squares.** Claude Opus 5.5 Max added both
  cases and reorganized the library by `n`.
* **Around 23:30 — simplification.** Claude Opus 5.5 Max reviewed the whole
  library, removed duplicated arguments and shared the common lemmas across
  cases.

## 23 September 2026

* **16:15 to 21:40 — seven squares.** ChatGPT 6 Pro wrote an analytic proof
  of the seven-square optimum, with its sliding family of optimal packings,
  without compiling it
  ([PR #4](https://github.com/vltanh/lean4-squares-in-circles/pull/4)).
  Claude Opus 5.5 Max compiled it and added it to the library.
