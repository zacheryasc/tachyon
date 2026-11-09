# Tachyon

The Tachyon shielded transaction protocol for Zcash.

## Architecture

### Transaction Structure

A **bundle** contains actions, a value balance, and a binding signature.
Each **action** carries a value commitment (`cv`), a randomized verification
key (`rk`), and a spend authorization signature (`sig`).

**Tachygrams** (nullifiers and note commitments) live in the **stamp**, not
in the action. This separation enables stamp stripping during proof
aggregation while actions retain their authorization.

```mermaid
classDiagram
    class Bundle["Bundle&lt;Stamp&gt;"] {
        actions: Action[]
        value_balance: i64
        binding_sig: BindingSignature
        stamp: Stamp
    }
    class Action {
        cv: value::Commitment
        rk: RandomizedVerificationKey
        sig: SpendAuthSignature
    }
    class Stamp {
        tachygrams: Tachygram[]
        anchor: Anchor
        proof: Proof
    }
    Bundle *-- Action
    Bundle *-- Stamp
```

## Status

Core cryptographic plumbing is implemented and tested:

- Key derivation (PRF^expand with sign normalization)
- Value commitments (Pedersen over Pallas, shared generators with Orchard)
- Spend authorization signatures (RedPallas, randomized keys)
- Binding signatures (value balance enforcement via homomorphic commitments)
- Bundle construction and signature verification

Stubbed (pending Ragu PCD and Poseidon integration):

- Note commitments
- Nullifier derivation (GGM tree PRF)
- Proof creation, merge, and verification
- Stamp compression/decompression

## Proof applications

`zcash_tachyon::stamp::proof::new_application()` returns a boxed Ragu application
with Tachyon's baked parameters and registry tags. Retain the owner in each
proving or verification worker and pass `&application` before the RNG argument
to stamp proving, lifting, merging, unmerging, compression and verification.
Bundle lifting and proof verification take the same borrow.

Wallets pass the application when proving a stamp. Aggregators retain it while
transforming stamps. Zebra's mempool verification and miner aggregation workers
own their applications. Bundle parsing, signing, witness preparation and native
anchor advancement use their existing inputs. For real Ragu, keep each worker's
application on that worker because the application is not `Sync`.

## Development

Requires Rust stable (1.85+) and nightly for formatting/linting.

```sh
just test    # cargo test --workspace --features test-epoch-size
just lint    # cargo +nightly clippy --workspace --all-targets --features test-epoch-size
just fmt     # cargo +nightly fmt --all
just doc     # cargo doc --workspace --no-deps
```

## License

MIT OR Apache-2.0
