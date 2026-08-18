<div align="center">

# norn

**a reactive language for servers**

*Functional reactive programming, structured concurrency, server I/O, and ownership,<br>
designed as one coherent model — and compiled to native binaries.*

</div>

---

A `reactor` is a live dependency graph. Inputs arrive as discrete occurrences, state advances in atomic turns, signals recompute glitch-free, and effects run only after a turn commits — so no observer ever sees a half-updated world.

```
task fn report(open: I64) -> ()
    uses { clock }
{
    await sleep(1)
    print(open)
}

reactor Gate(limit: I64)
    uses { clock }
{
    input opened: () [capacity: 64, overflow: reject]
    input closed: () [capacity: 64, overflow: reject]

    state accepted: I64 = 0
    state released: I64 = 0

    on opened() {
        accepted = accepted + 1
        if accepted - released > limit {
            after report(accepted - released)
        }
    }

    on closed() {
        released = released + 1
    }

    signal open = accepted - released
    export signal healthy = open <= limit
}
```

## Try it

```sh
make install                              # build the compiler and link ~/.cargo/bin/norn
norn run examples/reactors/gate.norn      # check, lower, and execute
norn build examples/run/hello.norn -o hello   # compile to a native binary
```

## Status

Early, and honest about it. [DESIGN.md](./DESIGN.md) is the whitepaper — the language as it might be. [BOOTSTRAP.md](./BOOTSTRAP.md) is the implementation plan for a v0 subset, which today parses, type-checks, interprets, and compiles to native binaries — structs, enums, tasks, reactors, and ownership. HTTP is next.

The same program runs under the interpreter and as a native binary, and the two must produce byte-identical event traces — that differential oracle is the test harness.

## License

[MIT](LICENSE)
