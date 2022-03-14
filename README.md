**Kong**

Kong provides one thing, `kong`, which is a version of `cong` that
automatically figures out its first argument, i.e., where in a goal to apply
the equality given by its second argument.

It looks at the left-hand side of a goal, finds all occurrences of the
equality's left-hand side in it, and constructs a function that applies the
equality to all of them.

This is more naive than what the standard library's `cong!` tactic does, which
compares the goal's left-hand and right-hand sides, figures out the differences,
and constructs a function that applies the equality exactly where the
differences are.

In my use cases, Kong's more naive approach seems a little more robust. It
handles, for example, turning `x + y` into `y + x`.

Note that the equality must not have any implicit or instance arguments left.
For example, to use `m*n%n≡0` you need to explicitly provide the `NonZero`
argument:

```
... ≡⟨ kong (m*n%n≡0 x d ⦃ d≢0 ⦄) ⟩
```
