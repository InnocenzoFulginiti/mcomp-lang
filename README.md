# µcomp-lang compiler
This project implements a statically typed, imperative programming language that supports component-based interfaces. The compiler is structured into two main parts: a frontend developed in **OCaml**, and a backend using **LLVM** to generate low-level code.

## Features

- Statically typed imperative language
- Support for component-based modular programming
- Type-checked interface definitions and implementations
- Separation between interface declaration and implementation
- LLVM IR code generation

## Technologies Used

- **OCaml** — Core language for frontend implementation
- **Ocamllex** — Lexical analyzer generator
- **Menhir** — Parser generator
- **LLVM** — Backend for low-level code generation

## Project Structure

- `src/` — Contains OCaml source files for lexer, parser, typechecker, and codegen
- `test/` — Sample programs written in the custom language
- `Makefile` — For building the project
- `report.pdf` — Detailed description of language design and implementation

## Building

Make sure you have OCaml, LLVM, Ocamllex, and Menhir installed. Then run:

```bash
make
