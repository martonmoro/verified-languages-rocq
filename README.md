# Verified small languages in Rocq

Two small programming languages formalized in the
[Rocq Prover](https://rocq-prover.org/), with machine-checked proofs that their
tools and programs behave correctly.

## Razor: a verified compiler

[`Razor.v`](Razor.v) defines a typed language of numbers and booleans, then proves:

| Theorem | Statement |
|---|---|
| `opt_correct` | Constant folding does not change a term's value. |
| `compile_correct` | Running the compiled code on the stack machine leaves exactly the term's value on the stack. |
| `compile_opt_correct` | The same holds when the term is optimised first. |

The key step is `comp_correct`, whose induction keeps the stack and the
continuation general because subterms run with different ones.

## System T: functions and iteration

[`SystemT.v`](SystemT.v) adds functions, variables and iteration over natural
numbers. Terms are typed and use de Bruijn indices, and a recursive evaluator
gives each term its meaning as a Rocq function.

| Result | Statement |
|---|---|
| `iter_add` | Iterating `m + n` times equals iterating `n` times and then `m` times. |
| `double_correct` | `double` returns `n + n` for every `n`. |
| `parity_double` | `parity` returns 0 for every doubled number. |
| `ack_1_1`, `ack_2_3`, `ack_3_3` | The Ackermann function, written in System T, gives the expected values. |

The Ackermann examples are checked on specific inputs only.

## Build

Requires Rocq 9.1 and its standard library (`opam install rocq-prover`).

```sh
make
```

The build succeeds only if every proof checks. No proofs are admitted.
`opt_correct` and `compile_opt_correct` use the `dependent destruction` tactic,
so they depend on the standard axiom `eq_rect_eq`. `compile_correct` and the
checked System T results use no axioms.

## License

MIT
