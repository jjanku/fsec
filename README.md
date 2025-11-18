# Formalization of the Forking Lemma and Fiat-Shamir Transformation in EasyCrypt

See the [eprint](https://eprint.iacr.org/2025/573) for more details about this project.

## Setup

The project is checked using [EasyCrypt 2025.11](https://github.com/EasyCrypt/easycrypt/releases/tag/r2025.11), see [CI setup](./.github/workflows/ci.yaml). Required SMT solvers can be found in [easycrypt.project](easycrypt.project). (Other versions may work as well. Or not.)

More detailed installation instructions can be found on [EasyCrypt's GitHub](https://github.com/EasyCrypt/easycrypt).

## Verification

To check a single file, e.g., `proof/Forking.ec`, simply run:

```bash
easycrypt proof/Forking.ec
```

To check the whole project, use the following command:

```bash
easycrypt runtest tests.config proof
```

Note that this does not verify external dependencies (see [deps](./deps/)); to do so, replace `proof` by `deps` in the above.
