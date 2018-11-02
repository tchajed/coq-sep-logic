# Separation logic library

A basic library for separation logic in Coq.

Uses `A -> option V` as the basic representation of heaps with addresses `A` and values `V`. Addresses should have decidable equality for basic operations like heap updates to work.

## Compiling

This project uses [coq-project-template](https://github.com/tchajed/coq-project-template). You'll need to initialize a submodule with `git submodule update --init --recursive` and then `make` should just work.

## Depending on this library

If you're using the same setup you can add it as a dependency with

```
git submodule add https://github.com/tchajed/coq-sep-logic vendor/sep-logic
git submodule add https://github.com/tchajed/coq-tactical vendor/tactical
```