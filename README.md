# Rust BIP47 Library

This library implements the BIP47 standard and provides functionality
for generating static payment codes that two parties can use to create
a private payment address space between them.

Original specification: [BIP-0047](https://github.com/bitcoin/bips/blob/master/bip-0047.mediawiki).

## Usage
```rust
// Alice constructs her own payment code using a BIP32 seed and account 0
let alice_private = PrivateCode::from_seed(&alice_seed, Network::Bitcoin, Some(0), None).unwrap();

// Alice parses Bob's payment code
let bob_public = PublicCode::from_wif("PM8TJS2JxQ5ztXUpBBRnpTbcUXbUHy2T1abfrb3KkAAtMEGNbey4oumH7Hc578WgQJhPjBxteQ5GHHToTYHE3A1w6p7tU6KSoFmWBVbFGjKPisZDbP97").unwrap();

// Alice calculates Bob's receive address at index 0, known only to them. Address can either be P2PKH or P2WPKH
let bob_address_0 = bob_public.address(&alice_private, 0, AddressType::P2PKH).unwrap();

// Alice can now pay Bob privately
assert_eq!("12edoJAofkjCsWrtmVjuQgMUKJ6Z7Ntpzx", bob_address_0.to_string());

```

## MSRV
The minimum supported Rust version is **1.56.1**.
